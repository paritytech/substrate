extern crate cc;

fn main() {
    cc::Build::new()
        .file("src/driver/os_uart.c")
        .file("src/driver/crc.c")
        .file("src/driver/uart.c")
        .file("src/driver/io.c")
        .file("src/driver/solo.c")
        .compile("libsolo.a");
}
