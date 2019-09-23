int uart_init(int* dev);
int uart_write(unsigned char* data, int len);
int uart_read(unsigned char* data, int len); 
int uart_close();