#!/bin/bash

IMPORTS=`
  find . -name '*.agda' |
  sed -E -e 's|^\./(.*)\.agda|\1|' -e 's|/|.|g' |
  grep -v 'everything' |
  sort |
  sed -E -e 's/(.*)/open import \1 using ()/'`

perl -0777 -i -pe "s/(-- BEGIN IMPORTS\\n).*(\\n-- END IMPORTS)/\$1$IMPORTS\$2/s" everything.agda
