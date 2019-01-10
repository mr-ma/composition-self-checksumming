get_filename_component(self-checksumming_CMAKE_DIR "${CMAKE_CURRENT_LIST_FILE}" PATH)
include(CMakeFindDependencyMacro)

list(APPEND CMAKE_MODULE_PATH ${self-checksumming_CMAKE_DIR})

find_package(LLVM 7.0 REQUIRED CONFIG)
find_package(input-dependency REQUIRED COMPONENTS InputDependency)
find_package(nlohmann_json REQUIRED)
find_package(composition-framework REQUIRED)
find_package(function-filter REQUIRED)

list(REMOVE_AT CMAKE_MODULE_PATH -1)

set(self-checksumming_LIBRARIES self-checksumming::SCPass self-checksumming::SCPatchPass)
