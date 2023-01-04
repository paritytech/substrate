#!/bin/bash

set -e
# set -x
# trap read debug

args=$@
cargo build --release

# we do not need to use `useradd` to create another non-root user since we are
# using a pre-built image that has already created one called 'nonroot':
# see https://hub.docker.com/r/paritytech/ci-linux/tags > "production" > Layer 12 
usermod -u 1000 -s /bin/sh -d /var/www/node-template nonroot
mkdir -p /data /var/www/node-template/.local/share/node-template
# change owner to non-root user of static symlink directory for storing chain data 
chown -R nonroot:nonroot /data
# change owner to non-root user for hidden subdirectories of their home directory
chown -R nonroot:nonroot /var/www/node-template/.[^.]*
# change owner to non-root user for non-hidden subdirectories of their home directory
chown -R nonroot:nonroot /var/www/node-template

# ignore warning: `Not copying any file from skel directory into it.`
symlink=/var/www/node-template/.local/share/node-template/data
# create symlink if not already exist 
[ ! -L ${symlink} ] && ln -s /data /var/www/node-template/.local/share/node-template
# copy skel files to user nonroot home directory if it already exists
cp -r /etc/skel/. /var/www/node-template
# sanity checks
ldd -d -r -v /var/www/node-template/target/release/node-template

# switch to non-root user. show version of node-template.
su -c "printf \"\n*** Changed to the home directory ${PWD} of user: \" && id \
    && /var/www/node-template/target/release/node-template --version" nonroot

# handle when arguments not provided. run arguments provided to script.
if [ "$args" = "" ] ; then
    su -c "printf \"Note: Please try providing an argument to the script.\n\n\"" nonroot
    exit 1
else
    su -c "printf \"*** Running the provided arguments: $args\n\n\"" nonroot
    su -c "$args" nonroot
fi
