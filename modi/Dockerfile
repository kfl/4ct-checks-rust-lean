# Toolchain image for building the C++ reference binary as a linux/amd64 ELF,
# so it can run on MODI's x86_64 nodes. Ubuntu's apt ships a *matched*
# boost/spdlog/fmt set (spdlog 1.12 + fmt 9), avoiding the conda
# bundled-vs-standalone fmt version clash entirely.
#
# This image holds ONLY the toolchain — the source is MOUNTED at build time
# (no COPY), so the image is built once and cached, edit-rebuild is instant,
# and the output binary lands straight in your working tree.
#
#   # 1. Build the toolchain image once (no build context needed):
#   docker build --platform linux/amd64 -t cc-deps - < modi/Dockerfile
#
#   # 2. Build the binary with the repo mounted (into build-linux/, so it does
#   #    not clobber a macOS build/ tree). Only the `main` target -> googletest
#   #    is fetched+configured but never compiled:
#   docker run --rm --platform linux/amd64 -v "$PWD":/work -w /work cc-deps \
#     bash -c 'cmake -B build-linux -DCMAKE_BUILD_TYPE=Release && \
#              cmake --build build-linux --target main -j'
#   # -> build-linux/src/main   (linux/amd64 ELF)
#
#   # 3. Bundle the binary + its non-glibc .so deps (~1.5 MB) for shipping:
#   docker run --rm --platform linux/amd64 -v "$PWD":/work -w /work cc-deps bash -c '
#     mkdir -p /tmp/out/lib && cp build-linux/src/main /tmp/out/cpp_main
#     ldd build-linux/src/main | grep -oE "/[^ ]+\.so[.0-9]*" \
#       | grep -vE "/(libc|libm|libpthread|libdl|librt|ld-linux.*|libresolv|libgcc_s)\.so" \
#       | sort -u | xargs -I{} cp -L {} /tmp/out/lib/
#     tar czf - -C /tmp/out .' > cpp-bin.tgz
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential cmake ca-certificates \
        libboost-program-options-dev libboost-thread-dev \
        libspdlog-dev libfmt-dev \
 && rm -rf /var/lib/apt/lists/*
