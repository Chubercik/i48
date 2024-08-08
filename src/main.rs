use i48::i48;

fn main() {
    let a: i48 = 1000.into();
    let b: i48 = 2000.into();
    let c = a + b;

    println!("{} + {} = {}", a, b, c);
}
