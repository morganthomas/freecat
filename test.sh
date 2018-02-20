#!/bin/sh
echo "01-list"
./dist/build/freecat/freecat test/cases/01-list/context.fcat example
echo "02-list-implicit"
./dist/build/freecat/freecat test/cases/02-list-implicit/context.fcat example
echo "03-list-partially-implicit"
./dist/build/freecat/freecat test/cases/03-list-partially-implicit/context.fcat example
