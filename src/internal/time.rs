use std::time::{Duration, SystemTime, UNIX_EPOCH};

// ========================================================================= //

/// Returns the current time as a CFB file timestamp (the number of
/// 100-nanosecond intervals since January 1, 1601 UTC).
pub fn current_timestamp() -> u64 {
    match SystemTime::now().duration_since(epoch()) {
        Ok(delta) => {
            delta.as_secs() * 10_000_000 + (delta.subsec_nanos() / 100) as u64
        }
        Err(_) => 0,
    }
}

/// Converts a CFB file timestamp to a local `SystemTime`.
pub fn system_time_from_timestamp(timestamp: u64) -> SystemTime {
    let delta = Duration::new(
        timestamp / 10_000_000,
        (timestamp % 10_000_000) as u32 * 100,
    );
    epoch() + delta
}

fn epoch() -> SystemTime {
    // The epoch used by CFB files is Jan 1, 1601 UTC, which we can calculate
    // from the Unix epoch constant, which is Jan 1, 1970 UTC.
    UNIX_EPOCH - Duration::from_secs(11644473600)
}

// ========================================================================= //

#[cfg(test)]
mod tests {
    use super::system_time_from_timestamp;
    use std::time::{Duration, UNIX_EPOCH};

    #[test]
    fn system_time() {
        let sat_18_mar_2017_at_18_46_36_gmt =
            UNIX_EPOCH + Duration::from_secs(1489862796);
        assert_eq!(
            system_time_from_timestamp(131343363960000000),
            sat_18_mar_2017_at_18_46_36_gmt
        );
    }
}

// ========================================================================= //
