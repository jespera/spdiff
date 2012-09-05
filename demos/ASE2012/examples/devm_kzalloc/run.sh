#!/bin/bash
spdiff.opt -macro_file standard.h -spatch -focus_function vpbe_probe -show_support -only_changes -filter_spatches
