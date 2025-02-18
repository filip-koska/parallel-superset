add_library(err err.c)
add_library(io io.c)
target_link_libraries(io PUBLIC err)
