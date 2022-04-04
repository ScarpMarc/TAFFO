export LLVM_DIR=/usr/lib/llvm-12/bin/
# Generate an LLVM file to analyze
"$LLVM_DIR"clang -O0 -emit-llvm -S ./input.c -o input.ll
# Run the pass through opt - New PM
"$LLVM_DIR"opt -S -load-pass-plugin ../../../build/lib/Taffo.so --passes="inject-func-call" input.ll -o instrumented.ll

"$LLVM_DIR"llc -filetype=obj instrumented.ll -o instrumented.o

"$LLVM_DIR"clang instrumented.o -o instrumented

./instrumented
