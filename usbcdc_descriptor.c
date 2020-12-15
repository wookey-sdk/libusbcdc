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
#include "libc/arpa/inet.h"
#include "libusbctrl.h"
#include "usbcdc.h"
#include "usbcdc_descriptor.h"
#include "usbcdc_requests.h"


/*
 * This functional Desc is for CDC/ACM only
 */
static full_functional_desc_t funcdesc = {
    .header = {
        .bLength = sizeof(header_functional_desc_t),
        .bDescriptorType = CS_INTERFACE_DESC,
        .bDescriptorSubtype = CS_FUNCTIONAL_HEADER,
        .bcdCDC_hi = CDC_VERSION_Hi,
        .bcdCDC_lo = CDC_VERSION_Lo
    },
    .call = {
        .bFunctionLength = sizeof(call_mgmt_functional_desc_t),
        .bDescriptorType = CS_INTERFACE_DESC,
        .bDescriptorSubtype = CS_FUNCTIONAL_CALL,
        .bmCapabilities = CALL_MGMT_CAPA_NONE,
        .bDataInterface = 0x01   /* Data interface id, to be updated after declaration */
    },
    .acm = {
        .bFunctionLength = sizeof(acm_functional_desc_t),
        .bDescriptorType = CS_INTERFACE_DESC,
        .bDescriptorSubtype = CS_FUNCTIONAL_ACM,
        .bmCapabilities = ACM_CAPA_LINE_CODING_SUPPORT
    },
    .un = {
        .bFunctionLength = sizeof(union_functional_desc_t),
        .bDescriptorType = CS_INTERFACE_DESC,
        .bDescriptorSubtype = CS_FUNCTIONAL_UNION,
        .bMasterInterface = 0x00, /* iface 0: CDC control */
        .bSlaveInterface0 = 0x01  /* iface 1: CDC data */
    }
};

mbed_error_t      usbcdc_get_descriptor(uint8_t             iface_id,
                                        uint8_t            *buf,
                                        uint8_t            *desc_size,
                                        uint32_t            usbdci_handler __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    usbcdc_context_t *ctx = usbcdc_get_context();
    if (buf == NULL || desc_size == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (iface_id == ctx->cdc_ifaces[0].iface.id) {
        uint8_t my_desc_len = sizeof(funcdesc);
        uint8_t to_copy = my_desc_len > *desc_size ? *desc_size : my_desc_len;
        memcpy(buf, (uint8_t*)&funcdesc, to_copy);
        *desc_size = to_copy;
    } else {
        *desc_size = 0;
    }
err:
    return errcode;
}
