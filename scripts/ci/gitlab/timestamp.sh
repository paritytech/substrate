# https://gist.github.com/altaua/477285db40181ef1793bbed5bae32c6b
# based on https://gist.github.com/jstine35/e0fc0e06ec06d74bc3ebd67585bf2a1d

s_datestamp() {
  TZ=UTC
  eof=""
  while [[ -z "${eof}" ]]; do
    IFS="" read -r line || eof=1
    printf '[%(%F %T)T] %s\n' -1 "${line}"
  done
}

cleanup() {
  exec >/dev/null 2>&1
  wait "${TIMESTAMP_PID}"
}

exec > >(s_datestamp) 2>&1

TIMESTAMP_PID=$!
trap cleanup EXIT
