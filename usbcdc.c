/*
 *
 * Copyright 2019 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */


#include "api/libusbhid.h"
#include "libc/string.h"
#include "libc/sync.h"
#include "libusbctrl.h"
#include "usbhid.h"
#include "usbhid_requests.h"
#include "usbhid_reports.h"
#include "usbhid_descriptor.h"
#include "usbhid_default_handlers.h"
#include "libc/sanhandlers.h"


static bool data_being_sent = false;

static cdc_context_t usbcdc_ctx = { 0 };


static inline uint8_t get_in_epid(usbctrl_interface_t const * const iface)
{
    uint8_t epin = 0;
    uint8_t iface_ep_num = 0;
    /* sanitize */
    if (iface == NULL) {
        goto err;
    }
    if (iface->usb_ep_number >= MAX_EP_PER_INTERFACE) {
        goto err;
    }
    iface_ep_num = iface->usb_ep_number;
    /*@ assert iface_ep_num < MAX_EP_PER_INTERFACE ; */

    uint8_t i = 0;
    /*@
      @ loop invariant 0 <= i <= iface_ep_num ;
      @ loop assigns i ;
      @ loop variant (iface_ep_num - i);
      */
    for (i = 0; i < iface_ep_num; ++i) {
        if (iface->eps[i].dir == USB_EP_DIR_IN || iface->eps[i].dir == USB_EP_DIR_BOTH) {
            log_printf("[USBHID] IN EP is %d\n", iface->eps[i].ep_num);
            epin = iface->eps[i].ep_num;
            goto err;
        }
    }
err:
    return epin;
}


static mbed_error_t usbcdc_received(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t iface = 0;
    log_printf("[USBCDC] Huint8_t ID packet (%d B) received on ep %d\n", size, ep_id);


    for (iface = 0; iface < usbcdc_ctx.num_iface; ++iface)
    {
        if (usbcdc_ctx.hid_ifaces[iface].iface.usb_ep_number >= MAX_EP_PER_INTERFACE) {
            errcode = MBED_ERROR_INVPARAM;
            goto err;
        }

        uint8_t ep = 0;
        const uint8_t max_ep_number = usbcdc_ctx.cdc_ifaces[iface].iface.usb_ep_number;

        for (ep = 0; ep < max_ep_number; ++ep)
        {
            if (usbcdc_ctx.cdc_ifaces[iface].iface.eps[ep].ep_num == ep_id)
            {
                log_printf("[USBCDC] executing trigger for EP %d\n", ep_id);
                /* FIXME: upper layer trigger */
                goto err;
            }
        }
    }
err:
    return errcode;
}

static
mbed_error_t usbcdc_data_sent(uint32_t dev_id __attribute__((unused)), uint32_t size __attribute__((unused)), uint8_t ep_id __attribute((unused)))
{
    log_printf("[USBCDC] data (%d B) sent on EP %d\n", size, ep_id);
    set_bool_with_membarrier(&data_being_sent, false);
    return MBED_ERROR_NONE;
}


/*@
  @ assigns \nothing ;
  @ ensures \result == &usbcdc_ctx;
  */
usbhid_context_t *usbcdc_get_context(void)
{
    return (usbhid_context_t*)&usbhid_ctx;
}

bool usbcdc_interface_exists(uint8_t cdc_handler)
{
    usbcdc_context_t *ctx = usbcdc_get_context();
    bool result = false;
    if (cdc_handler < ctx->num_iface && cdc_handler < MAX_USBCDC_IFACES) {
        /* INFO: boolean normalization based on false (lonely checked value.
         * Thus, this is not fault-resilient as any non-zero value generates a
         * TRUE result */
        result = !(ctx->cdc_ifaces[cdc_handler].declared == false);
    }
    return result;
}

static mbed_error_t usbcdc_ep_trigger(uint32_t dev_id, uint32_t size, uint8_t ep_id)
{
    /* full duplex trigger, detect if the event on the EP is a IN event or an OUT event,
     * and call the corresponding function */

    usb_ep_dir_t dir;
    usb_backend_drv_ep_state_t state;
    mbed_error_t errcode;

    log_printf("[USBCDC] triggered on IN or OUT event\n");
    /* are we currently receiving content (DATA_OUT state ? */
    state = usb_backend_drv_get_ep_state(ep_id, USB_BACKEND_DRV_EP_DIR_OUT);
    if (state == USB_BACKEND_DRV_EP_STATE_DATA_OUT) {
        dir = USB_EP_DIR_OUT;
    } else {
        dir = USB_EP_DIR_IN;
    }
    /* otherwhise, we have been triggering on data sent */

    switch (dir) {
        case USB_EP_DIR_IN:
            log_printf("[USBCDC] triggered on IN event\n");
            errcode = usbcdc_data_sent(dev_id, size, ep_id);
            break;
        case USB_EP_DIR_OUT:
            log_printf("[USBCDC] triggered on OUT event\n");
            errcode = usbcdc_received(dev_id, size, ep_id);
            break;
        default:
            /* should never happend (dead block) */
            break;
    }
    return errcode;
}




mbed_error_t usbcdc_declare(uint32_t usbxdci_handler,
                            usbcdc_subclass_t cdc_subclass,
                            usbcdc_protocol_t cdc_protocol,
                            uint16_t          ep_mpsize,
                            uint8_t          *cdc_handler,
                            uint8_t          *in_buff,
                            uint32_t          in_buff_len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (cdc_handler == NULL) {
        log_printf("[USBHID] error ! hid_handler is null!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (usbcdc_ctx.num_iface >= MAX_USBCDC_IFACES) {
        log_printf("[USBHID] error ! no more iface storage !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff == NULL) {
        log_printf("[USBHID] error ! buffer given is null !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff_len == 0) {
        log_printf("[USBHID] error ! buffer given is null-sized !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }


    uint8_t i = usbcdc_ctx.num_iface;
    memset((void*)&usbcdc_ctx.cdc_ifaces[i], 0x0, sizeof(usbctrl_interface_t));

    ADD_LOC_HANDLER(usbcdc_class_rqst_handler);
    ADD_LOC_HANDLER(usbcdc_get_descriptor);
    ADD_LOC_HANDLER(usbcdc_data_sent);
    ADD_LOC_HANDLER(usbcdc_received);

    usbcdc_ctx.cdc_ifaces[i].iface.usb_class = USB_CLASS_CDC;
    usbcdc_ctx.cdc_ifaces[i].iface.usb_subclass = cdc_subclass; /* SCSI transparent cmd set (i.e. use INQUIRY) */
    usbcdc_ctx.cdc_ifaces[i].iface.usb_protocol = cdc_protocol; /* Protocol BBB (Bulk only) */
    usbcdc_ctx.cdc_ifaces[i].iface.dedicated = false;
    usbcdc_ctx.cdc_ifaces[i].iface.rqst_handler = usbcdc_class_rqst_handler;
    usbcdc_ctx.cdc_ifaces[i].iface.class_desc_handler = usbcdc_get_descriptor;

    uint8_t curr_ep = 0;

        /*
         * IN EP for low latency data transmission with the host
         */
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_BULK;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_IN;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].pkt_maxsize = ep_mpsize; /* mpsize on EP1 */
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].ep_num      = 1; /* this may be updated by libctrl */
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].handler     = usbcdc_data_sent;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].poll_interval = 0:
        curr_ep++;

        /*
         * IN & OUT dedicated EP for low latency data transmission with the host
         */
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_BULK;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_OUT;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].pkt_maxsize = ep_mpsize; /* mpsize on EP1 */
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].ep_num      = 1; /* this may be updated by libctrl */
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].handler     = usbcdc_received;
        usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].poll_interval = 0;
        curr_ep++;

    }

    /* @ assert curr_ep <= 2 ; */
    usbcdc_ctx.cdc_ifaces[i].iface.usb_ep_number = curr_ep;


    errcode = usbctrl_declare_interface(usbxdci_handler, (usbctrl_interface_t*)&(usbcdc_ctx.cdc_ifaces[i].iface));
    if (errcode != MBED_ERROR_NONE) {
        log_printf("[USBHID] Error while declaring interface: err=%d !\n", errcode);
        goto err;
    }

    /* set IN EP real identifier */
    uint8_t epid = get_in_epid(&usbcdc_ctx.cdc_ifaces[i].iface);
    usbcdc_ctx.cdc_ifaces[i].inep.id = epid;

    /* set current interface effective identifier */
    usbcdc_ctx.cdc_ifaces[i].id   = usbcdc_ctx.hid_ifaces[i].iface.id;
    usbcdc_ctx.cdc_ifaces[i].in_buff = in_buff;
    usbcdc_ctx.cdc_ifaces[i].in_buff_len = in_buff_len;

    /* the configuration step not yet passed */
    usbcdc_ctx.cdc_ifaces[i].configured = false;
    usbcdc_ctx.cdc_ifaces[i].declared = true;

    *cdc_handler = usbcdc_ctx.num_iface;
    usbcdc_ctx.num_iface++;
    request_data_membarrier();

err:
    return errcode;
}

mbed_error_t usbcdc_configure(uint8_t               cdc_handler,
                              usbcdc_received_t     cdc_receive_frame,
                              usbcdc_send_t         cdc_send_frame)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbcdc_context_t *ctx = usbhid_get_context();
    /* sanitize */
    if (!usbcdc_interface_exists(cdc_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (cdc_receive_frame == NULL || cdc_send_frame == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert errcode==MBED_ERROR_NONE; */
    /* set each of the interface callbacks */
    ctx->cdc_ifaces[cdc_handler].receive_frame_cb = cdc_receive_frame;
    ctx->cdc_ifaces[cdc_handler].send_frame_cb = cdc_send_frame;
    /* set interface as configured */
    ctx->cdc_ifaces[cdc_handler].configured = true;

err:
    return errcode;
}

#if 0
mbed_error_t usbhid_response_done(uint8_t hid_handler)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (!usbhid_interface_exists(hid_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    uint8_t epid = get_in_epid(&usbhid_ctx.hid_ifaces[hid_handler].iface);
    usb_backend_drv_send_zlp(epid);
err:
    return errcode;
}
#endif

mbed_error_t usbcdc_send_data(uint8_t              cdc_handler,
                              uint8_t*             response,
                              uint8_t              response_len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (response == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (response_len == 0) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (!usbcdc_interface_exists(cdc_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    while (data_being_sent == true) {
        request_data_membarrier();
    }

    set_bool_with_membarrier(&data_being_sent, true);
    /* total size is report + report id (one byte) */
    uint8_t epid = get_in_epid(&usbcdc_ctx.cdc_ifaces[hid_handler].iface);
    log_printf("[USBCDC] sending response on EP %d (len %d)\n", epid, response_len);

    errcode = usb_backend_drv_send_data(response, response_len, epid);
    if (errcode != MBED_ERROR_NONE) {
        goto err_send;
    }
    /* wait for end of transmission */
    while (data_being_sent == true) {
        request_data_membarrier();
    }
err_send:
    set_bool_with_membarrier(&data_being_sent, false);
err:
    return errcode;
}

