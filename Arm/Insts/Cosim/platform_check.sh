#!/bin/bash

# Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Author(s): Shilpi Goel

# Note: we return 1 when we have an Arm machine.
machine_check () {
    machine=$(uname -m)
    # Most Arm Linux machines use aarch64; some Arm Darwin machines
    # use arm64.
    if [[ $machine == *aarch64* || $machine == *arm64* ]]; then
	return 1
    else
	return 0
    fi
}

# Note: we return 1 when we have a Darwin machine.
is_darwin () {
    os=$(uname -s)
    if [[ $os == *Darwin* ]]; then
	return 1
    else
	return 0
    fi
}

# Note: we return 1 when the requested feature is supported.
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
	return 1
    else
	return 0
    fi
}

while getopts ":df:m" option; do
   case $option in
      d) # Check if the platform is Darwin
	  is_darwin
	  exit;;
      f) # Enter a feature (convert to lower case)
	  FEAT=$(echo "$OPTARG" | tr '[:upper:]' '[:lower:]')
	  feat_check
	  exit;;
      m) # Execute machine_check
	 machine_check
	 exit;;
     \?) # Invalid option
	 echo "platform_check error: Invalid option!"
	 exit;;
   esac
done
