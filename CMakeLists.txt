# Specify the minimum version for CMake
CMAKE_MINIMUM_REQUIRED(VERSION 3.2)

# Project's name 
PROJECT(Kunlun)

set(OPENSSL_USE_STATIC_LIBS TRUE)

FIND_PACKAGE(OpenSSL REQUIRED)
FIND_PACKAGE(OpenMP REQUIRED)

SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14 -fpic -Wno-deprecated-declarations -Wno-unused-result -Xpreprocessor -O3")

INCLUDE_DIRECTORIES(
    ${OPENSSL_INCLUDE_DIR}
    "/usr/local/include"
)

LINK_DIRECTORIES(
    /usr/local/lib64
)

SET(EXECUTABLE_OUTPUT_PATH ${PROJECT_SOURCE_DIR}/build) 

include(CMakePrintHelpers)

foreach(key
  IN ITEMS
    NUMBER_OF_LOGICAL_CORES
    NUMBER_OF_PHYSICAL_CORES
    IS_64BIT
    HAS_SSE2
    OS_NAME
    OS_RELEASE
  )
  # query the item ${key} and save its value in the variable _${key}
  cmake_host_system_information(RESULT _${key} QUERY ${key})
  cmake_print_variables(_${key})
endforeach()

# let the preprocessor know about the system name
if(CMAKE_SYSTEM_NAME  STREQUAL "Linux")
  SET(IS_LINUX 1)
endif()
if(CMAKE_SYSTEM_NAME  STREQUAL "Darwin")
  SET(IS_MACOS 1)
endif()
if(CMAKE_SYSTEM_NAME  STREQUAL "Windows")
  SET(IS_WINDOWS 1)
endif()

configure_file(${PROJECT_SOURCE_DIR}/config/config.h.in ${PROJECT_SOURCE_DIR}/config/config.h @ONLY)

# close warning
add_definitions(-w)

# netio
ADD_EXECUTABLE(test_netio test/test_netio.cpp)
TARGET_LINK_LIBRARIES(test_netio ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# ske  
ADD_EXECUTABLE(test_aes test/test_aes.cpp)
TARGET_LINK_LIBRARIES(test_aes ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# pke  
ADD_EXECUTABLE(test_twisted_elgamal test/test_twisted_elgamal.cpp)
TARGET_LINK_LIBRARIES(test_twisted_elgamal ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_elgamal test/test_elgamal.cpp)
TARGET_LINK_LIBRARIES(test_elgamal ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_calculate_dlog test/test_calculate_dlog.cpp)
TARGET_LINK_LIBRARIES(test_calculate_dlog ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# signature
ADD_EXECUTABLE(test_schnorr_sig test/test_schnorr_sig.cpp)
TARGET_LINK_LIBRARIES(test_schnorr_sig ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_accountable_ring_sig test/test_accountable_ring_sig.cpp)
TARGET_LINK_LIBRARIES(test_accountable_ring_sig ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# filter
ADD_EXECUTABLE(test_bloom_filter test/test_bloom_filter.cpp)
TARGET_LINK_LIBRARIES(test_bloom_filter ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_cuckoo_filter test/test_cuckoo_filter.cpp)
TARGET_LINK_LIBRARIES(test_cuckoo_filter ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# ot
ADD_EXECUTABLE(test_naor_pinkas_ot test/test_naor_pinkas_ot.cpp)
TARGET_LINK_LIBRARIES(test_naor_pinkas_ot ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_iknp_ote test/test_iknp_ote.cpp)
TARGET_LINK_LIBRARIES(test_iknp_ote ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_alsz_ote test/test_alsz_ote.cpp)
TARGET_LINK_LIBRARIES(test_alsz_ote ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)


# psi
ADD_EXECUTABLE(test_cwprf_psi test/test_cwprf_psi.cpp)
TARGET_LINK_LIBRARIES(test_cwprf_psi ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# pso
ADD_EXECUTABLE(test_mqrpmt test/test_mqrpmt.cpp)
TARGET_LINK_LIBRARIES(test_mqrpmt ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_mqrpmt_psi test/test_mqrpmt_psi.cpp)
TARGET_LINK_LIBRARIES(test_mqrpmt_psi ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_mqrpmt_psi_card test/test_mqrpmt_psi_card.cpp)
TARGET_LINK_LIBRARIES(test_mqrpmt_psi_card ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_mqrpmt_psi_card_sum test/test_mqrpmt_psi_card_sum.cpp)
TARGET_LINK_LIBRARIES(test_mqrpmt_psi_card_sum ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_mqrpmt_psu test/test_mqrpmt_psu.cpp)
TARGET_LINK_LIBRARIES(test_mqrpmt_psu ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_mqrpmt_private_id test/test_mqrpmt_private_id.cpp)
TARGET_LINK_LIBRARIES(test_mqrpmt_private_id ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# oprf
ADD_EXECUTABLE(test_oteoprf test/test_oteoprf.cpp)
TARGET_LINK_LIBRARIES(test_oteoprf ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# peqt
ADD_EXECUTABLE(test_peqt test/test_peqt.cpp)
TARGET_LINK_LIBRARIES(test_peqt ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# misc
ADD_EXECUTABLE(test_misc test/test_misc.cpp)
TARGET_LINK_LIBRARIES(test_misc ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)
  

# nike
ADD_EXECUTABLE(test_nizk_enc_relation test/test_nizk_enc_relation.cpp)
TARGET_LINK_LIBRARIES(test_nizk_enc_relation ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_nizk_dlog_knowledge test/test_nizk_dlog_knowledge.cpp)
TARGET_LINK_LIBRARIES(test_nizk_dlog_knowledge ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_nizk_plaintext_equality test/test_nizk_plaintext_equality.cpp)
TARGET_LINK_LIBRARIES(test_nizk_plaintext_equality ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_nizk_plaintext_knowledge test/test_nizk_plaintext_knowledge.cpp)
TARGET_LINK_LIBRARIES(test_nizk_plaintext_knowledge ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_nizk_dlog_equality test/test_nizk_dlog_equality.cpp)
TARGET_LINK_LIBRARIES(test_nizk_dlog_equality ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# bulletproof
ADD_EXECUTABLE(test_innerproduct_proof test/test_innerproduct_proof.cpp)
TARGET_LINK_LIBRARIES(test_innerproduct_proof ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

ADD_EXECUTABLE(test_bullet_proof test/test_bullet_proof.cpp)
TARGET_LINK_LIBRARIES(test_bullet_proof ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# gadget
ADD_EXECUTABLE(test_range_proof test/test_range_proof.cpp)
TARGET_LINK_LIBRARIES(test_range_proof ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# cryptocurrency
ADD_EXECUTABLE(test_adcp test/test_adcp.cpp)
TARGET_LINK_LIBRARIES(test_adcp ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# many out of many
ADD_EXECUTABLE(test_momproof test/test_momproof.cpp)
TARGET_LINK_LIBRARIES(test_momproof ${OPENSSL_LIBRARIES} OpenMP::OpenMP_CXX)

# mcl
# add_executable(test_mcl test/test_mcl.cpp)
# target_link_libraries(test_mcl libmcl.a libgmp.a)

