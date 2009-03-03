#!/bin/bash
# time ../../spdiff.opt -specfile specfile -top 14 -depth 4 -fixed -strict -prune $@
time ../../spdiff.opt -specfile specfile -depth 8 -fixed -strict  $@
