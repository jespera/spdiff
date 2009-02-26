#!/bin/bash
# time ../../spdiff.opt -specfile specfile -top 14 -depth 4 -fixed -strict -prune $@
time ../../spdiff -specfile specfile -depth 6 -fixed -strict  $@
