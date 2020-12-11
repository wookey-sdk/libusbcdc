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
#include "api/libusbhid.h"
#include "libusbctrl.h"
#include "libc/types.h"
#include "libc/stdio.h"
#include "usbhid.h"
#include "usbhid_descriptor.h"
#include "usbhid_reports.h"
#include "autoconf.h"

/* USBHID class specific request (i.e. bRequestType is Type (bit 5..6 = 1, bits 0..4 target current iface
 * These values are set in bRequest field */
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

static mbed_error_t usbhid_handle_std_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    /* get the high byte */
    uint8_t maxlen = pkt->wLength & 0xff;
    uint8_t action = pkt->bRequest;
    uint8_t descriptor_type = pkt->wValue >> 0x8;
    uint8_t descriptor_index = pkt->wValue & 0xff;
    usbcdc_context_t *ctx = usbhid_get_context();
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    switch (action) {
        default:
            log_printf("[USBHID] Unsupported class request action %x", action);
            errcode = MBED_ERROR_INVPARAM;
    }
err:
    return errcode;
}

static mbed_error_t usbhid_handle_class_request(usbctrl_setup_pkt_t *pkt)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbhid_context_t *ctx = usbcdc_get_context();
    if (ctx == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    uint8_t iface = pkt->wIndex & 0xff;

    uint8_t action = pkt->bRequest;
    switch (action) {
        case USB_CDC_RQST_SEND_ECAPSULATED_CMD:
            break;
        case USB_CDC_RQST_GET_ENCAPSULATED_CMD:
            break;
        default:
            log_printf("[USBHID] Ubsupported class request action %x", action);
            errcode = MBED_ERROR_INVPARAM;
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
