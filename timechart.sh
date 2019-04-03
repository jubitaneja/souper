echo "" > time-data.txt

last_count=0
last_size_count=0

while :
do
time=`date --rfc-3339=seconds`

active_count=`grep "total static profile" $1 | wc -l`

active_size_count=`grep "size" $1 | awk -F "= " '{ SUM += $2} END { print SUM }'`

if [ -z "$active_size_count" ]; then
  active_size_count=0
fi

echo "$time current_count=$active_count previous_count=$last_count current_size_count=$active_size_count previous_size_count=$last_size_count" >> time-data.txt

last_count=$active_count
last_size_count=$active_size_count


check_done=`grep "Done" $1`
if [ ! -z "$check_done" ]; then
  break
fi


echo "" >> time-data.txt
sleep 1
done
