# for folder in "/Users/fmora/Documents/software/eudoxus/docs/data/HuthRyan" "/Users/fmora/Documents/software/eudoxus/docs/data/LeeSeshia" "/Users/fmora/Documents/software/eudoxus/docs/data/BaierKatoen" 
for folder in "/Users/fmora/Documents/software/eudoxus/docs/data/LeeSeshia" "/Users/fmora/Documents/software/eudoxus/docs/data/BaierKatoen" 
do
    # for each file in the data directory that ends in .txt
    for file in $folder/*.txt
    do
        filename=$(basename -- "$file")
        date=$(date +"%m-%d-%Y")

        dir="results/$date"
        mkdir -p "$dir"

        output="$dir/$filename"
        output="${output/.txt/.ucl}"
        summary="$dir/$filename"
        echo "python3 self-repair-generate.py $file &> $summary"
        python3 self-repair-generate.py $file &> $summary
        sleep 10
    done
done