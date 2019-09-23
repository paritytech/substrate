#define CRC_OK          0
#define CRC_NOK         1
#define CRC_PARA_ERR    2

UINT32 check_crc(UINT8* data, UINT32 len, UINT8* crc);
UINT32 calc_crc(UINT8* data, UINT16 len, UINT8* crc);
