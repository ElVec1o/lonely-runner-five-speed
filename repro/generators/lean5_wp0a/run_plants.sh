#!/bin/bash
cd /DEV_TREE/work/lean5_wp0a
B=./target/release/wp0a_v5; C=../lean5_cert; D=out/plant_cert
{
for k in drop_t2 drop_t3 t3_witness t4_range t5_drop t2c_swap t1_h; do $B mutate $C $D $k; echo "PLANT file-level $k -> $($B check $D | cut -c1-110)"; done
for p in 1 2 3 4 5 6 7 8; do echo "PLANT memory-level --plant $p -> $($B check $C --plant $p | cut -c1-110)"; done
echo "PLANT raw byte flip in t3_000 without manifest update -> $($B check $C --flipbyte | cut -c1-110)"
echo "PLANT rho 3/5 in checker (weaker window lower bound) -> $($B check $C --rho 3/5 | cut -c1-110)"
echo "PLANT rho 9/10 in checker (stronger lower bound) -> $($B check $C --rho 9/10 | cut -c1-110)"
echo "CONTROL unmodified -> $($B check $C | cut -c1-30)"
} > out/plants.txt 2>&1
echo done >> out/plants.txt
