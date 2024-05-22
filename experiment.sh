# for folder in "data/HuthRyan" "data/LeeSeshia"
for folder in "data/BaierKatoen" "data/HuthRyan" "data/LeeSeshia"
do
    # for each file in the data directory that ends in .txt
    for file in $folder/*.txt
    do
        filename=$(basename -- "$file")
        date=$(date +"%m-%d-%Y-%H-%M")

        dir="results/$date"
        mkdir -p "$dir"

        output="$dir/$filename"
        output="${output/.txt/.ucl}"
        summary="$dir/$filename"
        echo "eudoxus --iterations 5 $file --output $output --model gpt-3.5-turbo-0125 &> $summary"
        eudoxus --iterations 5 $file --output $output --model gpt-3.5-turbo-0125 &> $summary
        sleep 10
    done
done
