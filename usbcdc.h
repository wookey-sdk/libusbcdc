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
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef USBCDC_H_
#define USBCDC_H_

#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/syscall.h"
#include "api/libusbcdc.h"
#include "libusbctrl.h"
#include "autoconf.h"

#if CONFIG_USR_LIB_USBCDC_DEBUG && !__FRAMAC__
# define log_printf(...) printf(__VA_ARGS__)
#else
# define log_printf(...)
#endif

#define MAX_USBCDC_IFACES    4

typedef struct {
    uint8_t  id;      /* IN EP identifier */
} usbcdc_inep_t;

/*
 * Each USB HID interface is composed of:
 * - an interface id (used to determine which interface is called by the host), set by libxDCI,
 *   as other classes may declare interfaces to libxDCI
 * - a usbctrl_interface_t structure, passed to the lower libxDCI interface
 * - an IN EP specific HID level meta-properties, associated to the IN EP declared in the
 *   usbctrl_interface_t
 * - various callbacks for standard HID requests
 * - a 'configured' flag, which control that the interface has been properly set and
 *   configured.
 */
typedef struct {
    uint8_t id;
    usbcdc_inep_t         inep; /* start at 1 (descriptor id start at 1) */
    usbctrl_interface_t   iface;
    uint8_t              *in_buff;
    bool                  configured;
    bool                  declared;
} usbcdc_iface_t;


/*
 * A USB HID context may have one or more concurrent HID interface(s).
 * These interfaces are declared successively.
 */
typedef struct {
    uint8_t               num_iface; /* number of reports */
    usbcdc_iface_t        hid_ifaces[MAX_USBCDC_IFACES];
} usbcdc_context_t;


#endif

usbcdc_context_t *usbcdc_get_context(void);

bool usbcdc_interface_exists(uint8_t cdc_handler);

#endif/*!USBCDC_H_*/
