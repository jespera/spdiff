#!/bin/bash

time ../../spdiff.opt -specfile specfile -patterns -depth 7 -top 25 2> err_out  -abstractness 2 $@
