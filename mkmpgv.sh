git archive HEAD -o mpgv.zip
zip -d mpgv.zip theories/locks
zip -d mpgv.zip theories/locks/*
zip -d mpgv.zip theories/sessiontypes
zip -d mpgv.zip theories/sessiontypes/*
zip -d mpgv.zip theories/lambdabar
zip -d mpgv.zip theories/lambdabar/*
zip -d mpgv.zip README.md
zip -d mpgv.zip mkmpgv.sh
mv README.md README_tmp.md
cp theories/multiparty/README.md README.md
zip -r mpgv.zip README.md README.md
rm README.md
mv README_tmp.md README.md
scp -P 5555 mpgv.zip artifact@localhost:mpgv.zip