use std::env;
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader};
use std::process::Command;
use goldenfile::Mint;

#[test]
fn golden_tests() -> io::Result<()> {
    fs::create_dir_all("tests/example_output")?;
    let mut mint = Mint::new("tests/example_output");

    let default_flags = vec!["--validate-only".to_owned()];

    // Make sure the binary is up to date
    let cargo_exe = env::var("CARGO").unwrap_or_else(|_| "cargo".to_owned());
    let output = Command::new(&cargo_exe)
        .arg("build")
        .arg("--release")
        .output()?;
    assert!(output.status.success());

    for entry in fs::read_dir("examples")? {
        let entry = entry?;
        let path = entry.path();

        let is_yaml = path.extension().map_or(false, |ext| ext == "yaml");
        if !is_yaml {
            continue;
        }

        let mut custom_flags = Vec::new();
        let mut has_custom_flags = false;

        let mut f = BufReader::new(File::open(&path)?);
        for line in f.lines() {
            let line = line?;
            let line = line.trim();
            if let Some(rest) = strip_prefix(line, "## FLAGS: ") {
                has_custom_flags = true;
                for part in rest.split_whitespace() {
                    custom_flags.push(part.to_owned());
                }
            }
        }

        let mut dest = mint.new_goldenfile(
            path.with_extension("out").file_name().unwrap(),
        )?;

        eprintln!("running {:?}", path);
        // TODO: use witness-checker builder as a library instead of invoking the binary
        let output = Command::new("target/release/cheesecloth")
            .arg(&path)
            .arg("--check-steps").arg("1")
            .args(if has_custom_flags { &custom_flags } else { &default_flags })
            .stdout(dest.try_clone()?)
            .stderr(dest)
            .output()?;
        assert!(output.status.success(), "failed on test {:?}", path);
    }

    // Check the contents of the `dest` files against the golden files.
    drop(mint);

    Ok(())
}

fn strip_prefix<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    if s.starts_with(prefix) {
        Some(&s[prefix.len()..])
    } else {
        None
    }
}
