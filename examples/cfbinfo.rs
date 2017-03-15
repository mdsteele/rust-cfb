extern crate cfb;

use cfb::CompoundFile;
use std::env;
use std::fs::File;

fn main() {
    if env::args().count() != 2 {
        println!("Usage: cfbinfo <path>");
        return;
    }
    let path = env::args().nth(1).unwrap();
    let file = File::open(path).unwrap();
    let comp = CompoundFile::open(file).unwrap();
    let mut stack = vec![comp.entry("/").unwrap()];
    while let Some(entry) = stack.pop() {
        println!("{:?} ({} bytes)", entry.path(), entry.len());
        if entry.is_storage() {
            stack.extend(comp.read_storage(entry.path()).unwrap());
        }
    }
}
