# CMake generated Testfile for 
# Source directory: F:/Repos/remodel
# Build directory: F:/Repos/remodel/out/build/x64-Debug
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test([=[remodel-unittests]=] "remodel_run_unittests")
set_tests_properties([=[remodel-unittests]=] PROPERTIES  _BACKTRACE_TRIPLES "F:/Repos/remodel/CMakeLists.txt;35;add_test;F:/Repos/remodel/CMakeLists.txt;0;")
subdirs("testing/gtest-1.7.0")
