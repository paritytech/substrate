# Original script from: https://gist.github.com/jstine35/e0fc0e06ec06d74bc3ebd67585bf2a1d
# By @jstine35 on GitHub


s_datestamp() {
    while read -r line; do
        timestamp=$(date -u '+%Y-%m-%d %H:%M:%S')

        # by nature BASH might run process subst twice when using >&2 pipes. This is a lazy
        # way to avoid dumping two timestamps on the same line:
        if [[ "$line" != \[${timestamp%% *}* ]]; then
            echo "[$timestamp] $line"
        else
            echo "$line"
        fi
    done
}

exec 1> >(s_datestamp)
exec 2> >(s_datestamp)
