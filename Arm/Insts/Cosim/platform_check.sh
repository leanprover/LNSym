#!/bin/bash

# Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Shilpi Goel

machine_check () {
    machine=$(uname -m)
    -- Most Arm Linux machine use aarch64; some Arm Darwin machines use arm64.
    if [[ $machine == *aarch64* || $machine == *arm64* ]]; then
	return 0
    else
	return 1
    fi
}

feat_check () {
    os=$(uname -s)
    if [[ $os == *Linux* ]]; then
	feat_support=$(lscpu | grep -c $FEAT)
    elif [[ $os == *Darwin* ]]; then
	# Convert feature to upper case and prefix with "FEAT_".
	local feature="FEAT_"$(echo "$FEAT" | tr '[:lower:]' '[:upper:]')
	feat_support=$(sysctl -a  | grep -c $feature)
    else
	echo "Unsupported platform: "$os
	exit 1
    fi

    if [[ feat_support -ne 0 ]]; then
	return 0
    else
	return 1
    fi
}

while getopts ":mf:" option; do
   case $option in
      m) # Execute machine_check
	 machine_check
	 exit;;
      f) # Enter a feature (convert to lower case)
	  FEAT=$(echo "$OPTARG" | tr '[:upper:]' '[:lower:]')
	  feat_check
	  exit;;
     \?) # Invalid option
	 echo "platform_check error: Invalid option!"
	 exit;;
   esac
done
