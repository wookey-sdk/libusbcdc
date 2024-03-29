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
#ifndef LIBUSBCDC_H_
#define LIBUSBCDC_H_

#include "libc/types.h"
#include "libc/syscall.h"
#include "libusbctrl.h"
#include "autoconf.h"

/******************
 * Triggers various standard HID requests to upper stack
 */
/*
 * USB HID class is defined here:
 * https://www.usb.org/sites/default/files/documents/hid1_11.pdf
 */

/***********************************************************
 * prototypes definitions
 */

/***********************************************************
 * Upper layer-defined callbacks
 *
 * On HID devices, it is complicated to handle upper layer functions as protoypes,
 * because such paradigm implies that there is a single upper HID stack being
 * executed in the same time.
 *
 *
 * As a consequence, the HID stack must handle upper layer calls through registered
 * callbacks, based on the interface registration. The HID stack will then
 * call, in the upper example, the FIDO callbacks or the keyboard callbacks when
 * receiving events:
 *
 *
 * [ACM(1)][ ISBN(2) ]
 *      ^    ^
 *      |    |
 * [   USB CDC(1+2)  ]
 *    ^          ^
 *    |          |
 * [ driver   ][ xDCI]
 *
 * Above the CDC stack, multiple callbacks are required. They are strictly typed
 * for security reason.
 */


typedef mbed_error_t (*usb_cdc_receive_t)(uint8_t cdc_handler, uint8_t *frame, uint16_t len);
typedef mbed_error_t (*usb_cdc_sent_t)(uint8_t cdc_handler);

/*
 * INFO:
 *
 * Get_Idle handling is directly returned by the HID stack, which keeps a copy of the
 * idle_ms value declared by the upper stack and potentially updated by the host.
 * This is required to handle silent mode during the HID device lifetime.
 *
 * As a consequence, the Get_Idle() event is not pushed to upper stacks.
 */

/**********************************************************************************
 * USB CDC stack API
 */


/*
 * Declaring the CDC interface against the USBCtrl plane.
 * The USBCtrl plane must have been configured previously (usbxdci_handler must be valid)
 */
mbed_error_t usbcdc_declare(__in  uint32_t          usbxdci_handler,
                            __in  uint16_t          data_mpsize,
                            __out uint8_t          *cdc_handler,
                            __in  uint8_t          *data_buf,
                            __in  uint32_t          data_buf_len);


mbed_error_t usbcdc_configure(uint8_t                     cdc_handler,
                              bool                        stty_mode,
                              usb_cdc_receive_t           cdc_receive_data_frame,
                              usb_cdc_sent_t              cdc_data_sent,
                              usb_cdc_sent_t              cdc_ctrl_sent);


/*
 * Initialize communication layer. To be executed **after** USB Control start and
 * SetConfiguration received but before the usbcdc_exec() loop.
 */
void usbcdc_initialize(uint8_t cdc_handler);

/*
 * Handle a signe CDC_DATA+CDC_CTRL handling loop associated with the given cdc_handler.
 * When using multiple interfaces (multiple cdc_handler), execute multiple usbcdc_exec()
 * each with one handler in the same exec loop.
 */
mbed_error_t usbcdc_exec(uint8_t cdc_handler);

/*
 * Activate the OUT Data endpoint. Inform the host that we can receive data on
 * CDC_DATA interface.
 */
void usbcdc_recv_data(uint8_t cdc_handler);


/*
 * Sending data on CDC_DATA class associated to given cdc_handler
 */
mbed_error_t usbcdc_send_data(uint8_t              cdc_handler,
                              uint8_t*             data,
                              uint8_t              data_len);


/*
 * Sending control informations on CDC_CTRL class associated to given cdc_handler
 */
mbed_error_t usbcdc_send_ctrl(uint8_t              cdc_handler,
                              uint8_t*             ctrl,
                              uint8_t              ctrl_len);

/***********************************************************
 * triggers
 *
 * On some HID specific events (received requests or transmition complete,
 * the upper stack may wish to receive event acknowledgement. They can
 * react to this events the way they want, using the upper API or just by
 * doing nothing.
 * There is two types of triggers:
 * - transmition done trigger (when HID data has been sent asynchronously
 *   on the IN interrupt EP)
 * - request received trigger (when the host has requested a HID specific information,
 *   handled at HID stack level). These requests may impact the upper stack which can,
 *   in consequence, react in the trigger.
 */
void usbcdc_data_sent_trigger(uint8_t cdc_handler, uint8_t index);


#endif/*!LIBUSBHID*/
