#!/bin/sh
# Run ONLY on Linux, in this lane's remote directory. No system installation.
# The 47 release tarball still contains #870. Apply the local continuity repair.
set -eu
[ "$(uname -s)" = Linux ] || { echo 'Linux build host required' >&2; exit 1; }
root_dir=$(pwd)
mkdir -p engine47
cd engine47
curl -fL --retry 2 https://downloads.sourceforge.net/project/ngspice/ng-spice-rework/47/ngspice-47.tar.gz -o ngspice-47.tar.gz
echo '894e649651f1838a14095e5a5439e7d3aa63e87ede14d283173fda4fcdef675f  ngspice-47.tar.gz' | sha256sum -c -
sha256sum ngspice-47.tar.gz > source.sha256
tar -xzf ngspice-47.tar.gz
cd ngspice-47
patch -p1 < "$root_dir/engine/diode-sidewall-continuity.patch"
./configure --prefix="$root_dir/engine47/install" --without-x --with-readline=no --enable-xspice --disable-openmp --disable-debug
make -j4
make install
"$root_dir/engine47/install/bin/ngspice" -v
