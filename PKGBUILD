# Maintainer: csicar (gmail)

pkgname=stverificationstudio
pkgver=1.1
pkgrel=1
pkgdesc="Graphical Structured Text verifier"
arch=('any')
url="https://git.scc.kit.edu/peese/stverificationstudio/"
license=("GPLv3")
depends=('java-runtime')
makedepends=('unzip')
source=("http://localhost:8080/artifacts.zip")

package() {
  mkdir -p "$pkgdir/opt/"
  cp --recursive "$srcdir/stvs" "$pkgdir/opt/$pkgname"

ls $pkgdir/opt/$pkgname/
  chmod 755 "$pkgdir/opt/$pkgname/stverificationstudio"
  install -D -m0644 "$pkgdir/stverificationstudio.desktop"
  "$pkgdir/usr/share/applications/stverificationstudio.desktop"
  mkdir -p "$pkgdir/usr/bin"
  ln -s "/opt/$pkgname/stverificationstudio" "$pkgdir/usr/bin/stverificationstudio"
}

md5sums=('SKIP')