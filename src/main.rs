use std::fs::File;
use std::io::{self, BufWriter};
use scale_isa;
use scale_isa::types::RegClearModp;

use cheesecloth::builder::Builder;


fn main() -> io::Result<()> {
    let mut b = Builder::default();

    {
        let r = b.ld::<RegClearModp>(1234);
        b.print(r);
    }

    let instrs = b.finish();
    let mut f = BufWriter::new(File::create("out.bc")?);
    for i in instrs {
        scale_isa::functions::write_instruction(&mut f, i)?;
    }

    Ok(())
}
