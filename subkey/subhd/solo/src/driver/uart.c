#include "def.h"
#include "uart.h"

UINT32 SOLO_uart_write(
    UINT8    *data,
    UINT16    len
)
{
#if (_SOLO_PLATFORM== _SOLO_LINUX_)
    UINT32 rv = 0;
    rv = uart_write(data,len);
    if(rv>0)
        return SOLO_OK;
    else
        return SOLO_ERROR_COMM;
#elif 0
#endif

}

UINT32 SOLO_uart_read(
    UINT8    *data,
    UINT16    len
)
{
#if (_SOLO_PLATFORM== _SOLO_LINUX_)
    UINT32 rv = 0;
    rv = uart_read(data,len);
    if(rv>0)
        return SOLO_OK;
    else
        return SOLO_ERROR_COMM;
#elif 0
#endif
}