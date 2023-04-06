#!/usr/bin/env bash

# fix awk decimal number parser
export LANG=en_US.UTF-8

if [[ -z $FORMAT ]]; then
  FORMAT='%40s %12s %12s%12s%12s\n'
fi


match_time()
{
  regex='^kernel[^0-9]*([^ ]+)'
  if [[ ( $1 =~ $regex ) ]]; then
    echo ${BASH_REMATCH[1]}
  else
    echo -1
  fi
}

benchmark=kmeans

for f in ./../common/img/*.rgb
do
  filename=$(basename "$f")
  extension="${filename##*.}"
  filename="${filename%.*}"
  
  mfloat=$(match_time "`cat data/output/${filename}_${benchmark}_time.txt`")
  mfix=$(match_time "`cat data/output/${filename}_${benchmark}_time-taffo.txt`")

  ./../common/scripts/png2rgb.py png data/output/${filename}_${benchmark}.rgb data/output/${filename}_${benchmark}.png > out1.tmp
  ./../common/scripts/png2rgb.py png data/output/${filename}_${benchmark}.rgb.fixp data/output/${filename}_${benchmark}.fixp.png > out2.tmp
  
  compare -metric RMSE data/output/${filename}_${benchmark}.png data/output/${filename}_${benchmark}.fixp.png /dev/null > tmp.log 2> tmp.err
  mrel_error=$(awk '{ printf("%0.6f", substr($2, 2, length($2) - 2) * 100) }' tmp.err)
  
  printf "$FORMAT" "${benchmark}_${filename}" $mfix $mfloat "$mrel_error" '-'
done
