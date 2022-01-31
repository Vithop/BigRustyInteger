#Welcome to the Big Rusty Integer Library!

##Getting started 
To get started with this project please make sure you have [Rust](https://www.rust-lang.org/) installed with cargo and ready to go!

##Setup
To setup the project run the following to update your dependencies. 
```
cargo update 
```
Then to build
```
cargo b
```
Lastly to build and run.
```
cargo r
```
##Benchmark
Coming soon!

##Example usage
This library is made with the goal of creating a Big Integer implementation which is as easy to use as primitive types so please use it as you would regular primitive types. 

Although despite my best efforts this is still not feature complete so here are some example usage.

*Note* As I am still learning Rust we will have to live with using move operands on any operation as doing copy's are expensive and I don't know how to move structs without using the move operand.


##Add
```
let mut a = BigInt::new(vec![u64::MAX,u64::MAX,u64::MAX]);
let mut b = BigInt::new(vec![2,2,2]);

a += &b;

let c:BigInt = &a + &b;
```
##Multiply
```
let d = &a * &b;
```
We also have a concurrent implementation of multiply for the really big Big Ints!
```
let e = BigInt::concurrent_slow_mul(&a, &b);
```