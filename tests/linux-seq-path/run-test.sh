#!/bin/bash
#time ../../spdiff.opt -specfile specfile -top 40 -depth 4 -fixed -strict -print_uniq -print_raw -prune -strip_eq
time ../../spdiff.opt -specfile specfile -top 40 -depth 4 -fixed -strict -threshold 2 $@
