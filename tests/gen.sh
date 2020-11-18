#!/usr/local/bin/bash

usage() {
    cat <<EOF
usage: $0 <N>
EOF
}

MODE=0

while getopts "htf" OPTCHAR; do
    case $OPTCHAR in
        "h")
            usage
            exit 0
            ;;
        "t")
            MODE=1
            ;;
        "f")
            MODE=0
            ;;
        "?")
            usage >&2
            exit 1
            ;;
    esac
done

shift $((OPTIND-1))

if [[ $# -ne 1 ]]; then
    usage >&2
    exit 1
fi

N="$1"
if [[ $MODE -eq 1 ]]; then
    BUG=$((RANDOM % N))
else
    BUG=-1
fi

cat <<EOF
#include <fcntl.h>
#include <unistd.h>

void fn(const char *path) {
EOF

for ((I=0;I<N;++I)); do
    if [[ $I -eq -$BUG ]]; then
        INIT=0
    else
        INIT=-1
    fi
    cat <<EOF
  int fd$I = $INIT;
EOF
done
    
cat <<EOF
EOF
for ((I=0;I<N;++I)); do
    cat <<EOF
  if ((fd$I = open(path, O_RDONLY)) < 0) {
    goto cleanup;
  }
EOF
done

cat <<EOF

 cleanup:
EOF

for ((I=0;I<N;++I)); do
    cat <<EOF
  if (fd$I >= 0) {
    close(fd$I);
  }
EOF
done

cat <<EOF
}
EOF
