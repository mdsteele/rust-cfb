extern crate cfb;
extern crate chrono;
extern crate clap;
extern crate uuid;

use chrono::NaiveDateTime;
use clap::{App, Arg, SubCommand};
use std::cmp;
use std::io;
use std::path::PathBuf;
use std::time::UNIX_EPOCH;
use uuid::Uuid;

fn split(path: &str) -> (PathBuf, PathBuf) {
    let mut pieces = path.splitn(2, ':');
    if let Some(piece1) = pieces.next() {
        if let Some(piece2) = pieces.next() {
            (PathBuf::from(piece1), PathBuf::from(piece2))
        } else {
            (PathBuf::from(piece1), PathBuf::new())
        }
    } else {
        (PathBuf::new(), PathBuf::new())
    }
}

fn list_entry(name: &str, entry: &cfb::Entry, long: bool) {
    if !long {
        println!("{}", entry.name());
        return;
    }
    let length = if entry.len() >= 10_000_000_000 {
        format!("{} GB", entry.len() / (1 << 30))
    } else if entry.len() >= 100_000_000 {
        format!("{} MB", entry.len() / (1 << 20))
    } else if entry.len() >= 1_000_000 {
        format!("{} kB", entry.len() / (1 << 10))
    } else {
        format!("{} B ", entry.len())
    };
    let last_modified = {
        let timestamp = cmp::max(entry.created(), entry.modified());
        let seconds = if timestamp > UNIX_EPOCH {
            timestamp.duration_since(UNIX_EPOCH).unwrap().as_secs() as i64
        } else {
            -(UNIX_EPOCH.duration_since(timestamp).unwrap().as_secs() as i64)
        };
        let naive = NaiveDateTime::from_timestamp(seconds as i64, 0);
        naive.date().format("%b %d %Y")
    };
    println!(
        "{}{:08x}   {:>10}   {}   {}",
        if entry.is_storage() { '+' } else { '-' },
        entry.state_bits(),
        length,
        last_modified,
        name
    );
    if entry.is_storage() {
        println!(" {}", entry.clsid().to_hyphenated());
    }
}

fn main() {
    let matches = App::new("cfbtool")
        .version("0.1")
        .author("Matthew D. Steele <mdsteele@alum.mit.edu>")
        .about("Inspects and modifies CFB files")
        .subcommand(
            SubCommand::with_name("cat")
                .about("Concatenates and prints streams")
                .arg(Arg::with_name("path").multiple(true)),
        )
        .subcommand(
            SubCommand::with_name("chcls")
                .about("Changes storage CLSIDs")
                .arg(Arg::with_name("clsid").required(true))
                .arg(Arg::with_name("path").multiple(true)),
        )
        .subcommand(
            SubCommand::with_name("ls")
                .about("Lists storage contents")
                .arg(
                    Arg::with_name("all")
                        .short("a")
                        .help("Includes . in output"),
                )
                .arg(
                    Arg::with_name("long")
                        .short("l")
                        .help("Lists in long format"),
                )
                .arg(Arg::with_name("path").multiple(true)),
        )
        .get_matches();
    if let Some(submatches) = matches.subcommand_matches("cat") {
        if let Some(paths) = submatches.values_of("path") {
            for path in paths {
                let (comp_path, inner_path) = split(path);
                let mut comp = cfb::open(&comp_path).unwrap();
                let mut stream = comp.open_stream(inner_path).unwrap();
                io::copy(&mut stream, &mut io::stdout()).unwrap();
            }
        }
    } else if let Some(submatches) = matches.subcommand_matches("chcls") {
        let clsid =
            Uuid::parse_str(submatches.value_of("clsid").unwrap()).unwrap();
        if let Some(paths) = submatches.values_of("path") {
            for path in paths {
                let (comp_path, inner_path) = split(path);
                let mut comp = cfb::open(&comp_path).unwrap();
                comp.set_storage_clsid(inner_path, clsid).unwrap();
                comp.flush().unwrap();
            }
        }
    } else if let Some(submatches) = matches.subcommand_matches("ls") {
        if let Some(paths) = submatches.values_of("path") {
            let long = submatches.is_present("long");
            for path in paths {
                let (comp_path, inner_path) = split(path);
                let comp = cfb::open(&comp_path).unwrap();
                let entry = comp.entry(&inner_path).unwrap();
                if entry.is_stream() {
                    list_entry(entry.name(), &entry, long);
                } else {
                    if submatches.is_present("all") {
                        list_entry(".", &entry, long);
                    }
                    for subentry in comp.read_storage(&inner_path).unwrap() {
                        list_entry(subentry.name(), &subentry, long);
                    }
                }
            }
        }
    }
}
