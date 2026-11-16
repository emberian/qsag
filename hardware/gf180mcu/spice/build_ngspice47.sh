#!/bin/sh
# Run ONLY on Linux, in this lane's remote directory. No system installation.
# ngspice 47 includes the upstream diode sidewall charge continuity repair #870.
set -eu
[ "$(uname -s)" = Linux ] || { echo 'Linux build host required' >&2; exit 1; }
root_dir=$(pwd)
mkdir -p engine47
cd engine47
curl -fL --retry 2 https://downloads.sourceforge.net/project/ngspice/ng-spice-rework/47/ngspice-47.tar.gz -o ngspice-47.tar.gz
sha256sum ngspice-47.tar.gz > source.sha256
tar -xzf ngspice-47.tar.gz
cd ngspice-47
./configure --prefix="$root_dir/engine47/install" --without-x --with-readline=no --enable-xspice --disable-openmp --disable-debug
make -j4
make install
"$root_dir/engine47/install/bin/ngspice" -v
