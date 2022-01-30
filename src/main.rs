extern crate num_traits;

use std::u64;
use big_rusty_integer::BigInt;

fn main() {
    println!("Hello, world!");
    println!("This is the Rusty Big Integer Library!");
    let mut a = BigInt::new(vec![u64::MAX,u64::MAX,u64::MAX]);
    let mut b = BigInt::new(vec![2,2,2]);
    // a.add(&b);
    a += &b;
    a.print_digits();
    b.print_digits();
    let c:BigInt = &a + &b;
    c.print_digits();
    println!(" _____");
    
    b *= u64::MAX;
    b.print_digits();

    println!(" _____");
    let d = &a * &b;
    d.print_digits();
    a.print_digits();
    b.print_digits();

    println!(" _____");
    let e = &a * &b;
    e.print_digits();
    a.print_digits();
    b.print_digits();
}
