#!/bin/bash
# Exploratory (not pre-registered): the ground truth on every std model rIC3 ran on,
#   not only those with pairs (P6).  bash study/p6_all_models.sh study/results > study/results/p6_all_models.csv
cd "$1" || exit 1
while IFS=, read -r m _ v; do
  f=corpus/models/$m.aag
  [ -f "$f" ] || { echo "$m,$v,missing"; continue; }
  g=$(python3 -I ../tools/bfs.py "$f" | awk '{print $1}')
  echo "$m,$v,$g"
done < ric3_verdicts.csv
