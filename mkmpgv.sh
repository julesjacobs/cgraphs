git archive HEAD -o sources.zip
zip -d sources.zip theories/multiparty
zip -d sources.zip theories/multiparty/*
zip -d sources.zip theories/locks/lambdalockpp
zip -d sources.zip theories/locks/lambdalockpp/*
zip -d sources.zip theories/sessiontypes
zip -d sources.zip theories/sessiontypes/*
zip -d sources.zip theories/lambdabar
zip -d sources.zip theories/lambdabar/*
zip -d sources.zip README.md
zip -d sources.zip mkmpgv.sh
# mv README.md README_tmp.md
# cp theories/multiparty/README.md README.md
# zip -r sources.zip README.md README.md
# rm README.md
# mv README_tmp.md README.md
# scp -P 5555 mpgv.zip artifact@localhost:mpgv.zip