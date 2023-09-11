use std::io;
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use time::OffsetDateTime;
use uuid::Uuid;

#[derive(Parser, Debug)]
#[clap(author, about, long_about = None)]
struct Cli {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Concatenates and prints streams
    Cat { path: Vec<String> },

    /// Changes storage CLSIDs
    Chcls { clsid: Uuid, path: Vec<String> },

    /// Lists storage contents
    Ls {
        #[clap(short, long)]
        /// Lists in long format
        long: bool,

        #[clap(short, long)]
        /// Includes . in output
        all: bool,

        path: Vec<String>,
    },
}

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
        let timestamp = entry.created().max(entry.modified());
        let datetime = OffsetDateTime::from(timestamp);
        let (year, month, day) = datetime.to_calendar_date();
        format!("{:04}-{:02}-{:02}", year, month as u8, day)
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
        println!(" {}", entry.clsid().hyphenated());
    }
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Command::Cat { path } => {
            for path in path {
                let (comp_path, inner_path) = split(&path);
                let mut comp = cfb::open(&comp_path).unwrap();
                let mut stream = comp.open_stream(inner_path).unwrap();
                io::copy(&mut stream, &mut io::stdout()).unwrap();
            }
        }
        Command::Chcls { clsid, path } => {
            for path in path {
                let (comp_path, inner_path) = split(&path);
                let mut comp = cfb::open(&comp_path).unwrap();
                comp.set_storage_clsid(inner_path, clsid).unwrap();
                comp.flush().unwrap();
            }
        }
        Command::Ls { long, all, path } => {
            for path in path {
                let (comp_path, inner_path) = split(&path);
                let comp = cfb::open(&comp_path).unwrap();
                let entry = comp.entry(&inner_path).unwrap();
                if entry.is_stream() {
                    list_entry(entry.name(), &entry, long);
                } else {
                    if all {
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
