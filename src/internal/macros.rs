// ========================================================================= //

macro_rules! invalid_data {
    ($e:expr) => {
        return Err(io::Error::new(io::ErrorKind::InvalidData, $e));
    };
    ($fmt:expr, $($arg:tt)+) => {
        return Err(io::Error::new(io::ErrorKind::InvalidData,
                                  format!($fmt, $($arg)+)));
    };
}

macro_rules! invalid_input {
    ($e:expr) => {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, $e));
    };
    ($fmt:expr, $($arg:tt)+) => {
        return Err(io::Error::new(io::ErrorKind::InvalidInput,
                                  format!($fmt, $($arg)+)));
    };
}

macro_rules! not_found {
    ($e:expr) => {
        return Err(io::Error::new(io::ErrorKind::NotFound, $e));
    };
    ($fmt:expr, $($arg:tt)+) => {
        return Err(io::Error::new(io::ErrorKind::NotFound,
                                  format!($fmt, $($arg)+)));
    };
}

// ========================================================================= //
