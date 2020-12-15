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


#include "api/libusbcdc.h"
#include "libc/string.h"
#include "libc/sync.h"
#include "libc/nostd.h"
#include "libc/sanhandlers.h"
#include "libusbctrl.h"
#include "usbcdc.h"
#include "usbcdc_requests.h"
#include "usbcdc_descriptor.h"


static bool data_being_sent = false;
static bool data_received = false;
static uint32_t received_size = 0;

static usbcdc_context_t usbcdc_ctx = { 0 };



uint8_t ctrlbuf[8];
uint16_t ctrlbuf_len = 8;

void usbcdc_prepare_rcv(uint8_t cdc_handler) {
    printf("set fifo for EP %d (in & out)\n", usbcdc_ctx.cdc_ifaces[cdc_handler+1].iface.eps[0].ep_num);
    /* on a TTY, we read a char */
    usb_backend_drv_set_recv_fifo(usbcdc_ctx.cdc_ifaces[cdc_handler+1].buf, 1,usbcdc_ctx.cdc_ifaces[cdc_handler+1].iface.eps[0].ep_num);
}

void usbcdc_recv_on_endpoints(uint8_t cdc_handler)
{
//    uint8_t it_ep = usbcdc_ctx.cdc_ifaces[cdc_handler].iface.usb_ep_number - 1;

    //usb_backend_drv_set_recv_fifo(usbcdc_ctx.cdc_ifaces[cdc_handler].buf, usbcdc_ctx.cdc_ifaces[cdc_handler].buf_len,usbcdc_ctx.cdc_ifaces[cdc_handler].iface.eps[it_ep].ep_num);
//    usb_backend_drv_activate_endpoint(usbcdc_ctx.cdc_ifaces[0].iface.eps[2].ep_num, USB_BACKEND_DRV_EP_DIR_OUT);

    /* Set BULK OUT Endpoint for reception. CDC-DATA is using single full duplex EP (2 pipes) */
    /* on a TTY, we read a char */
    usb_backend_drv_set_recv_fifo(usbcdc_ctx.cdc_ifaces[cdc_handler+1].buf, 1,usbcdc_ctx.cdc_ifaces[cdc_handler+1].iface.eps[0].ep_num);
    usb_backend_drv_activate_endpoint(usbcdc_ctx.cdc_ifaces[cdc_handler+1].iface.eps[0].ep_num, USB_BACKEND_DRV_EP_DIR_OUT);
    //bsb_backend_drv_activate_endpoint(usbcdc_ctx.cdc_ifaces[cdc_handler+1].iface.eps[0].ep_num, USB_BACKEND_DRV_EP_DIR_IN);

//    printf("activate endpoint %d\n", usbcdc_ctx.cdc_ifaces[1].iface.eps[0].ep_num);
}


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
            log_printf("[USBCDC] IN EP is %d\n", iface->eps[i].ep_num);
            epin = iface->eps[i].ep_num;
            goto err;
        }
    }
err:
    return epin;
}


static inline mbed_error_t usbcdc_received(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep_id)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t iface = 0;
    log_printf("[USBCDC] uint8_t ID packet (%d B) received on ep %d\n", size, ep_id);


    for (iface = 0; iface < usbcdc_ctx.num_iface; ++iface)
    {
        if (usbcdc_ctx.cdc_ifaces[iface].iface.usb_ep_number >= MAX_EP_PER_INTERFACE) {
            errcode = MBED_ERROR_INVPARAM;
            goto err;
        }

        uint8_t ep = 0;
        const uint8_t max_ep_number = usbcdc_ctx.cdc_ifaces[iface].iface.usb_ep_number;

        for (ep = 0; ep < max_ep_number; ++ep)
        {
            if (usbcdc_ctx.cdc_ifaces[iface].iface.eps[ep].ep_num == ep_id)
            {
                //log_printf("[USBCDC] executing trigger for EP %d\n", ep_id);
                //usbcdc_ctx.cdc_ifaces[iface].buf[size] = '\0';
                //log_printf("[USBCDC] received: %s\n", usbcdc_ctx.cdc_ifaces[iface].buf);
                /* FIXME: upper layer trigger */
                set_bool_with_membarrier(&data_received, true);
                set_u32_with_membarrier(&received_size, size);
                goto err;
            }
        }
    }
err:
    return errcode;
}

static inline
mbed_error_t usbcdc_data_sent(uint32_t dev_id __attribute__((unused)), uint32_t size __attribute__((unused)), uint8_t ep_id __attribute((unused)))
{
    //log_printf("[USBCDC] data (%d B) sent on EP %d\n", size, ep_id);
    set_bool_with_membarrier(&data_being_sent, false);
    return MBED_ERROR_NONE;
}

static
mbed_error_t usbcdc_data_ep_handler(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep_id)
{
    usb_ep_dir_t dir;
    usb_backend_drv_ep_state_t state;
    mbed_error_t errcode;

    //log_printf("[USBCDC] triggered on IN or OUT event (ep %x)\n", ep_id);
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

/*@
  @ assigns \nothing ;
  @ ensures \result == &usbcdc_ctx;
  */
usbcdc_context_t *usbcdc_get_context(void)
{
    return (usbcdc_context_t*)&usbcdc_ctx;
}

bool usbcdc_interface_exists(uint8_t cdc_handler)
{
    usbcdc_context_t *ctx = usbcdc_get_context();
    bool result = false;
    if (cdc_handler < ctx->num_iface && cdc_handler < 2*MAX_USBCDC_FUNCTIONS) {
        /* INFO: boolean normalization based on false (lonely checked value.
         * Thus, this is not fault-resilient as any non-zero value generates a
         * TRUE result */
        result = !(ctx->cdc_ifaces[cdc_handler].declared == false);
    }
    return result;
}


static mbed_error_t usbcdc_declare_ctrl(uint32_t          usbxdci_handler,
                                        uint8_t          *cdc_handler,
                                        uint8_t          *in_buff,
                                        uint32_t          in_buff_len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (cdc_handler == NULL) {
        log_printf("[USBCDC] error ! hid_handler is null!\n");
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (usbcdc_ctx.num_iface >= 2*MAX_USBCDC_FUNCTIONS) {
        log_printf("[USBCDC] error ! no more iface storage !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff == NULL) {
        log_printf("[USBCDC] error ! buffer given is null !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff_len == 0) {
        log_printf("[USBCDC] error ! buffer given is null-sized !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }


    uint8_t i = usbcdc_ctx.num_iface;
    memset((void*)&usbcdc_ctx.cdc_ifaces[i], 0x0, sizeof(usbctrl_interface_t));

    ADD_LOC_HANDLER(usbcdc_class_rqst_handler);
    ADD_LOC_HANDLER(usbcdc_get_descriptor);
    ADD_LOC_HANDLER(usbcdc_data_rqst_recv);
    ADD_LOC_HANDLER(usbcdc_data_rqst_sent);
    ADD_LOC_HANDLER(usbcdc_get_descriptor);
    ADD_LOC_HANDLER(usbcdc_ctrl_send);

    usbcdc_ctx.rqstbuflen = 64;
    memset(usbcdc_ctx.rqstbuf, 0x0, 64);

    usbcdc_ctx.cdc_ifaces[i].iface.usb_class = USB_CLASS_CDC_CTRL;
    usbcdc_ctx.cdc_ifaces[i].iface.usb_subclass = 0x02; /* ACM Subclass */
    usbcdc_ctx.cdc_ifaces[i].iface.usb_protocol = 0x01; /*Common AT commands */
    usbcdc_ctx.cdc_ifaces[i].iface.dedicated = false;
    usbcdc_ctx.cdc_ifaces[i].iface.class_desc_handler = usbcdc_get_descriptor;
    usbcdc_ctx.cdc_ifaces[i].iface.rqst_handler = usbcdc_class_rqst_handler;
    usbcdc_ctx.cdc_ifaces[i].iface.composite_function = true;
    usbcdc_ctx.cdc_ifaces[i].iface.composite_function_id = 1;

    usbcdc_ctx.cdc_ifaces[i].buf = ctrlbuf;
    usbcdc_ctx.cdc_ifaces[i].buf_len = ctrlbuf_len;

    uint8_t curr_ep = 0;

    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_CONTROL,
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_OUT;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].pkt_maxsize = 64; /* mpsize on EP1 */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].ep_num      = 0; /* this may be updated by libctrl */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].handler     = usbcdc_data_rqst_recv;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].poll_interval = 16; /*0x10 ms in FS */
    curr_ep++;

    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_CONTROL,
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_IN;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].pkt_maxsize = 64; /* mpsize on EP1 */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].ep_num      = 0; /* this may be updated by libctrl */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].handler     = usbcdc_data_rqst_sent;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].poll_interval = 16; /*0x10 ms in FS */
    curr_ep++;

    /*
     * IN EP for low latency ctrl transmission with the host
     */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_INTERRUPT,
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_IN;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].pkt_maxsize = 8; /* mpsize on EP1 */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].ep_num      = 1; /* this may be updated by libctrl */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].handler     = usbcdc_ctrl_send;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].poll_interval = 16; /*0x10 ms in FS */
    curr_ep++;

    usbcdc_ctx.cdc_ifaces[i].iface.usb_ep_number = curr_ep;

    errcode = usbctrl_declare_interface(usbxdci_handler, (usbctrl_interface_t*)&(usbcdc_ctx.cdc_ifaces[i].iface));
    if (errcode != MBED_ERROR_NONE) {
        log_printf("[USBCDC] Error while declaring interface: err=%d !\n", errcode);
        goto err;
    }

    usbcdc_ctx.cdc_ifaces[i].iface.usb_ep_number = curr_ep;

    /* set current interface effective identifier */
    usbcdc_ctx.cdc_ifaces[i].id  = usbcdc_ctx.cdc_ifaces[i].iface.id;
    usbcdc_ctx.cdc_ifaces[i].buf = in_buff;
    usbcdc_ctx.cdc_ifaces[i].buf_len = in_buff_len;

    /* the configuration step not yet passed */
    usbcdc_ctx.cdc_ifaces[i].configured = false;
    usbcdc_ctx.cdc_ifaces[i].declared = true;

    *cdc_handler = usbcdc_ctx.num_iface; /* returning ctrl iface as handler */
    usbcdc_ctx.num_iface++;
    request_data_membarrier();
err:
    return errcode;

}



static mbed_error_t usbcdc_declare_data(uint32_t          usbxdci_handler,
                                        uint16_t          ep_mpsize,
                                        uint8_t          *in_buff,
                                        uint32_t          in_buff_len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* sanitize */
    if (usbcdc_ctx.num_iface >= 2*MAX_USBCDC_FUNCTIONS) {
        log_printf("[USBCDC] error ! no more iface storage !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff == NULL) {
        log_printf("[USBCDC] error ! buffer given is null !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    if (in_buff_len == 0) {
        log_printf("[USBCDC] error ! buffer given is null-sized !\n");
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }


    uint8_t i = usbcdc_ctx.num_iface;
    memset((void*)&usbcdc_ctx.cdc_ifaces[i], 0x0, sizeof(usbctrl_interface_t));

    ADD_LOC_HANDLER(usbcdc_class_rqst_handler);
    ADD_LOC_HANDLER(usbcdc_received);
    ADD_LOC_HANDLER(usbcdc_data_sent);
    ADD_LOC_HANDLER(usbcdc_data_ep_handler);

    uint8_t curr_ep = 0;

    usbcdc_ctx.cdc_ifaces[i].iface.usb_class = USB_CLASS_CDC_DATA;
    usbcdc_ctx.cdc_ifaces[i].iface.usb_subclass = 0x00;
    usbcdc_ctx.cdc_ifaces[i].iface.usb_protocol = 0x00;
    usbcdc_ctx.cdc_ifaces[i].iface.rqst_handler = NULL;
    usbcdc_ctx.cdc_ifaces[i].iface.class_desc_handler = NULL;
    usbcdc_ctx.cdc_ifaces[i].iface.dedicated = false;
    usbcdc_ctx.cdc_ifaces[i].iface.composite_function = true;
    usbcdc_ctx.cdc_ifaces[i].iface.composite_function_id = 1;



    /*
     * IN EP for low latency ctrl transmission with the host
     */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].type        = USB_EP_TYPE_BULK;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].dir         = USB_EP_DIR_BOTH;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].attr        = USB_EP_ATTR_NO_SYNC;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].usage       = USB_EP_USAGE_DATA;
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].pkt_maxsize = ep_mpsize; /* mpsize on EP1 */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].ep_num      = 2; /* this may be updated by libctrl */
    usbcdc_ctx.cdc_ifaces[i].iface.eps[curr_ep].handler     = usbcdc_data_ep_handler;

    curr_ep++;

    usbcdc_ctx.cdc_ifaces[i].iface.usb_ep_number = curr_ep;
    errcode = usbctrl_declare_interface(usbxdci_handler, (usbctrl_interface_t*)&(usbcdc_ctx.cdc_ifaces[i].iface));
    if (errcode != MBED_ERROR_NONE) {
        log_printf("[USBCDC] Error while declaring interface: err=%d !\n", errcode);
        goto err;
    }

    /* set current interface effective identifier */
    usbcdc_ctx.cdc_ifaces[i].id   = usbcdc_ctx.cdc_ifaces[i].iface.id;
    usbcdc_ctx.cdc_ifaces[i].buf = in_buff;
    usbcdc_ctx.cdc_ifaces[i].buf_len = in_buff_len;

    /* the configuration step not yet passed */
    usbcdc_ctx.cdc_ifaces[i].configured = false;
    usbcdc_ctx.cdc_ifaces[i].declared = true;

    usbcdc_ctx.num_iface++;
    request_data_membarrier();

err:
    return errcode;
}

mbed_error_t usbcdc_declare(uint32_t          usbxdci_handler,
                            uint16_t          data_mpsize,
                            uint8_t          *cdc_handler,
                            uint8_t          *data_buf,
                            uint32_t          data_buf_len,
                            uint8_t          *ctrl_buf,
                            uint16_t          ctrl_buf_len)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    if ((errcode = usbcdc_declare_ctrl(usbxdci_handler, cdc_handler, data_buf, data_buf_len)) != MBED_ERROR_NONE) {
        goto err;
    }
    /* FIXME data mpsize */
    errcode = usbcdc_declare_data(usbxdci_handler, data_mpsize, ctrl_buf, ctrl_buf_len);
err:
    return errcode;
}


mbed_error_t usbcdc_configure(uint8_t                   cdc_handler,
                              usb_cdc_receive_t         cdc_receive_data_frame,
                              usb_cdc_receive_t         cdc_receive_ctrl_frame)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbcdc_context_t *ctx = usbcdc_get_context();
    /* sanitize */
    if (!usbcdc_interface_exists(cdc_handler)) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (cdc_receive_data_frame == NULL || cdc_receive_ctrl_frame == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /*@ assert errcode==MBED_ERROR_NONE; */
    /* set each of the interface callbacks */
    //ctx->cdc_ifaces[cdc_handler].receive_frame_cb = cdc_receive_frame;
    /* set interface as configured */
    ctx->cdc_ifaces[cdc_handler].receive = cdc_receive_ctrl_frame;
    ctx->cdc_ifaces[cdc_handler+1].receive = cdc_receive_data_frame;
    ctx->cdc_ifaces[cdc_handler].configured = true;

err:
    return errcode;
}

mbed_error_t usbcdc_ctrl_send(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep_id)
{
    size = size;
    ep_id = ep_id;
    /* trigger upper layer */
    usbcdc_context_t *ctx = usbcdc_get_context();
    /* FIXME hardcoded */
    ctx->cdc_ifaces[0].receive(0, &ctx->cdc_ifaces[0].buf[0], size);
    /* frame received on control plane */
    return MBED_ERROR_NONE;
}

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

#if 0
    while (data_being_sent == true) {
        request_data_membarrier();
    }
#endif

    set_bool_with_membarrier(&data_being_sent, true);
    /* total size is report + report id (one byte) */
    uint8_t epid = get_in_epid(&usbcdc_ctx.cdc_ifaces[cdc_handler+1].iface);
    log_printf("[USBCDC] sending response on EP %d (len %d)\n", epid, response_len);

    errcode = usb_backend_drv_send_data(response, response_len, epid);
    if (errcode != MBED_ERROR_NONE) {
        goto err_send;
    }
    /* wait for end of transmission */
#if 0
    while (data_being_sent == true) {
        request_data_membarrier();
    }
#endif
err_send:
    set_bool_with_membarrier(&data_being_sent, false);
err:
    return errcode;
}

#if 0
/* FIXME extern volatile */
extern volatile bool rqst_data_received;
extern volatile bool rqst_data_sent;
extern volatile bool rqst_data_being_send;
extern volatile bool connected;
#endif

mbed_error_t usbcdc_exec(uint8_t cdc_handler)
{
    usbcdc_recv_on_endpoints(cdc_handler);
    /* is there async requests to handle ? */
#if 0
    if (rqst_data_received && !rqst_data_being_send) {
        log_printf("ack on EP0\n");
        rqst_data_received = false;
        usb_backend_drv_send_zlp(EP0);
    }
    if (rqst_data_sent) {
        rqst_data_being_send = false;
        rqst_data_sent = false;
    }
#endif
    /* inform host that we are ready to recv */
    //usbcdc_send_data(cdc_handler, (uint8_t*)"W", 1);
    /* and wait for command */
    if (data_received == true && received_size > 0) {
        /* hardcoded: should be passed to upper layer */
        usbcdc_ctx.cdc_ifaces[cdc_handler+1].buf[received_size] = '\0';
        /* acknowledge reception */
        set_bool_with_membarrier(&data_received, false);
        char received = usbcdc_ctx.cdc_ifaces[cdc_handler+1].buf[0];
        usbcdc_send_data(cdc_handler, (uint8_t*)&received, 1);
        if (received == '\r') {
            usbcdc_send_data(cdc_handler, (uint8_t*)"\nCANif> ", 8);
        }
        set_u32_with_membarrier(&received_size, 0);
    }
    request_data_membarrier();

    return MBED_ERROR_NONE;
}
