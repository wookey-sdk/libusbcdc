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
 * the Free Software Foundation; either version 3 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#include "libusbctrl.h"
#include "api/libusbcdc.h"
#include "libusbctrl.h"
#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/arpa/inet.h"
#include "libc/sync.h"
#include "usbcdc.h"
#include "autoconf.h"


#define USB_STD_RQST_ACTION_GET_DESCRIPTOR 0x06
#define USB_STD_RQST_ACTION_SET_DESCRIPTOR 0x07

#define USB_CDC_RQST_SEND_ECAPSULATED_CMD   0x00
#define USB_CDC_RQST_GET_ECAPSULATED_RESP   0x01
#define USB_CDC_RQST_SET_COMM_FEATURE       0x02
#define USB_CDC_RQST_GET_COMM_FEATURE       0x03
#define USB_CDC_RQST_CLEAR_COMM_FEATURE     0x04
#define USB_CDC_RQST_SET_LINE_CODING        0x20
#define USB_CDC_RQST_GET_LINE_CODING        0x21
#define USB_CDC_RQST_SET_CTRL_LINE_STATE    0x22
#define USB_CDC_RQST_SEND_BREAK             0x23

typedef struct __packed {
    uint32_t dwDTERate;
    uint8_t  bCharFormat;
    uint8_t  bParityType;
    uint8_t  bDataBits;
} line_encoding_t;



static uint8_t curr_cmd = 0;

volatile bool rqst_data_received = false;
volatile bool rqst_data_sent = false;
volatile bool rqst_data_being_send = false;

static mbed_error_t usbcdc_request_handler(uint8_t cmd, uint8_t* data,
                                           uint16_t len __attribute__((unused)),
                                           uint16_t index __attribute__((unused)))
{
    log_printf("received cmd code: %x\n", cmd);
    switch (cmd) {
        case USB_STD_RQST_ACTION_GET_DESCRIPTOR:
            break;
        case USB_STD_RQST_ACTION_SET_DESCRIPTOR:
            break;

        case USB_CDC_RQST_SEND_ECAPSULATED_CMD:
            break;
        case USB_CDC_RQST_GET_ECAPSULATED_RESP:
            break;
        case USB_CDC_RQST_SET_COMM_FEATURE:
            break;
        case USB_CDC_RQST_GET_COMM_FEATURE:
            break;
        case USB_CDC_RQST_CLEAR_COMM_FEATURE:
            break;
        case USB_CDC_RQST_SET_LINE_CODING:
            log_printf("set line coding\n");
            line_encoding_t *ec = (line_encoding_t*)data;
            ec->dwDTERate = htonl(1152500);
            ec->bCharFormat = 1;
            ec->bParityType = 0;
            ec->bDataBits = 8;
            break;
        case USB_CDC_RQST_GET_LINE_CODING:
            break;
        case USB_CDC_RQST_SET_CTRL_LINE_STATE:
            break;
        case USB_CDC_RQST_SEND_BREAK:
            break;
        default:
            break;
    }
    return MBED_ERROR_NONE;
}


/*
 * EP0 handler for DATA state (handling DATA event (reception, end of emission) on the
 * control plane.
 * These functions are triggered by the libusbctrl.
 */
mbed_error_t usbcdc_data_rqst_recv(uint32_t dev_id __attribute__((unused)),
                                   uint32_t size,
                                   uint8_t ep_id __attribute((unused)))
{
    /* TODO: no data handling by now... */
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbcdc_context_t *ctx = usbcdc_get_context();
    log_printf("handling data content received for cmd 0x%x:\n", curr_cmd);
    hexdump(&ctx->rqstbuf[0], size);
    rqst_data_received = true;
    /* FIXME: index not handled */
    errcode = usbcdc_request_handler(curr_cmd, &ctx->rqstbuf[0], size, 0);
    return errcode;
}

mbed_error_t usbcdc_data_rqst_sent(uint32_t dev_id __attribute__((unused)),
                                   uint32_t size __attribute__((unused)),
                                   uint8_t ep_id __attribute((unused)))
{
    /* TODO: no data handling by now... */
    mbed_error_t errcode = MBED_ERROR_NONE;
    rqst_data_sent = true;
    rqst_data_being_send = false;
    return errcode;
}


static mbed_error_t usbcdc_handle_std_request(usbctrl_setup_pkt_t *pkt)
{
    /* TODO: get_interface, set_interface */
    mbed_error_t errcode = MBED_ERROR_NONE;
    pkt = pkt;
    return errcode;
}

static mbed_error_t usbcdc_handle_class_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* get the high byte */
    uint8_t action = pkt->bRequest;
    uint16_t len = pkt->wLength;
    uint16_t index = pkt->wIndex;
    usbcdc_context_t *ctx = usbcdc_get_context();

    if (len > ctx->rqstbuflen) {
        log_printf("[classRqst] size %d too big\n", len);
        /* should nak */
        usb_backend_drv_stall(EP0, USB_BACKEND_DRV_EP_DIR_OUT);
        goto err;
    }
    set_u8_with_membarrier(&curr_cmd, action);

    if (len > 0) {
        if (pkt->bmRequestType & 0x80) {
            log_printf("[classRqst] send back resp\n");
            /* no data with request, but data requested. treat and respond on upper layer */
            // trigger rqst: action, len=0
            usbcdc_request_handler(action, &ctx->rqstbuf[0], len, index);
            /* sending back data set in buf by upper layer */
            usb_backend_drv_send_data(&ctx->rqstbuf[0], len, EP0);
            usb_backend_drv_ack(EP0, USB_BACKEND_DRV_EP_DIR_OUT);
        } else {
            log_printf("[classRqst] rqst with data: prepare to recv\n");
            /* TODO: wait for previous read step to finish ? */
            /* data received with request on EP0 */
            // async trigger rqst: action, len=pkt->wLength, buf=ctrlbuf
            usb_backend_drv_set_recv_fifo(&ctx->rqstbuf[0], len, EP0);
            usb_backend_drv_activate_endpoint(EP0, USB_BACKEND_DRV_EP_DIR_OUT);
            goto err;
        }
    } else {
        /* data-less request */
        usbcdc_request_handler(action, 0, 0, index);
        usb_backend_drv_send_zlp(EP0);
    }
err:
    return errcode;
}


/**
 * \brief Class request handling
 *
 * There is two ways requests can be received at this level:
 * through a class level request:
 *  - the bmRequestType class bit is set to 1, indicating that the request is targetting
 *    the current class. In this first case, all the HID requests are possible.
 * through a standard request, targeting one of our (HID) interfaces.
 *  - in that case, the setup packet respect the USB standard, and two USB requests
 *    can target the HID level: Get_Descriptor() and Set_Descriptor().
 *
 * The below function discriminate the way request is passed to HID level, and calls the
 * appropriate handler.
 *
 * @param packet Setup packet
 */
mbed_error_t usbcdc_class_rqst_handler(uint32_t usbxdci_handler __attribute__((unused)),
                                       usbctrl_setup_pkt_t *packet)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    log_printf("[classRqst] handling CDC rqst\n");
    if (((packet->bmRequestType >> 5) & 0x3) == 1) {
        /* class request */
        log_printf("[classRqst] handling CDC class rqst\n");
        errcode = usbcdc_handle_class_request(packet);
    } else {
        /* standard request targetting current iface */
        log_printf("[classRqst] handling CDC std rqst\n");
        errcode = usbcdc_handle_std_request(packet);
    }
    return errcode;
}
