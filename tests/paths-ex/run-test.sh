#!/bin/bash

time ../../spdiff.opt -specfile specfile -patterns -depth 7 -top 25 2>/dev/null  -abstractness 2 $@
