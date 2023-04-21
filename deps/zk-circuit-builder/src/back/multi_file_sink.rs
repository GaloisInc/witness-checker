use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use zki_sieve_v3::{self, PrivateInputs, PublicInputs, Relation};
use zki_sieve_v3::producers::sink::Sink;
use zki_sieve_v3::structs::types::Type;


struct MultiFile {
    dir_path: PathBuf,
    manifest_file: File,
    counter: usize,
}

impl MultiFile {
    pub fn new(dir_path: PathBuf) -> io::Result<MultiFile> {
        fs::create_dir_all(&dir_path)?;
        let manifest_file = File::create(dir_path.join("manifest.txt"))?;
        Ok(MultiFile {
            dir_path,
            manifest_file,
            counter: 0,
        })
    }

    pub fn create_file(&mut self) -> io::Result<File> {
        let name = format!("x{}.sieve", self.counter);
        self.counter += 1;
        let file_path = self.dir_path.join(&name);
        let f = File::create(&file_path)?;
        self.manifest_file.write_all(format!("{}\n", name).as_bytes())?;
        Ok(f)
    }
}


pub fn clean_workspace(workspace: impl AsRef<Path>) -> io::Result<()> {
    let workspace = workspace.as_ref();

    for entry in fs::read_dir(workspace)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            let mut removed_all = true;
            for entry in fs::read_dir(&path)? {
                let entry = entry?;
                let path = entry.path();
                if path.extension().map_or(false, |ext| ext == "sieve") {
                    fs::remove_file(path)?;
                } else {
                    removed_all = false;
                }
            }
            if removed_all {
                fs::remove_dir(path)?;
            }
        }
    }

    Ok(())
}


/// Store messages into files using conventional filenames inside of a workspace.
pub struct MultiFileSink {
    pub workspace: PathBuf,

    public_inputs_files: HashMap<Type, MultiFile>,
    private_inputs_files: HashMap<Type, MultiFile>,
    relation_file: MultiFile,
}

impl MultiFileSink {
    pub fn new_clean(workspace: &impl AsRef<Path>) -> io::Result<MultiFileSink> {
        fs::create_dir_all(workspace)?;
        clean_workspace(workspace)?;
        Self::new_no_cleanup(workspace)
    }

    pub fn new_no_cleanup(workspace: &impl AsRef<Path>) -> io::Result<MultiFileSink> {
        Ok(MultiFileSink {
            workspace: workspace.as_ref().to_path_buf(),

            public_inputs_files: HashMap::new(),
            private_inputs_files: HashMap::new(),
            relation_file: MultiFile::new(Self::relation_path(workspace))?,
        })
    }

    pub fn next_public_inputs_paths(&self) -> PathBuf {
        self.workspace.join(format!(
            "000_public_inputs_{}",
            self.public_inputs_files.len(),
        ))
    }

    pub fn public_inputs_paths(workspace: &impl AsRef<Path>, length: usize) -> Vec<PathBuf> {
        (0..length)
            .map(|count| {
                workspace
                    .as_ref()
                    .join(format!("000_public_inputs_{}", count))
            })
            .collect()
    }

    pub fn next_private_inputs_paths(&self) -> PathBuf {
        self.workspace.join(format!(
            "001_private_inputs_{}",
            self.private_inputs_files.len(),
        ))
    }

    pub fn private_inputs_paths(workspace: &impl AsRef<Path>, length: usize) -> Vec<PathBuf> {
        (0..length)
            .map(|count| {
                workspace
                    .as_ref()
                    .join(format!("001_private_inputs_{}", count))
            })
            .collect()
    }

    pub fn relation_path(workspace: &impl AsRef<Path>) -> PathBuf {
        workspace
            .as_ref()
            .join(format!("002_relation"))
    }

    pub fn print_filenames(&self) {
        Self::public_inputs_paths(&self.workspace, self.public_inputs_files.len())
            .iter()
            .for_each(|path| eprintln!("Writing {}", path.display()));
        Self::private_inputs_paths(&self.workspace, self.private_inputs_files.len())
            .iter()
            .for_each(|path| eprintln!("Writing {}", path.display()));
        eprintln!("Writing {}", Self::relation_path(&self.workspace).display());
    }

    fn get_public_inputs_multi_file(&mut self, type_value: Type) -> io::Result<&mut MultiFile> {
        if !self.public_inputs_files.contains_key(&type_value) {
            self.public_inputs_files.insert(
                type_value.clone(),
                MultiFile::new(self.next_public_inputs_paths())?,
            );
        }
        Ok(self.public_inputs_files.get_mut(&type_value).unwrap())
    }

    fn get_private_inputs_multi_file(&mut self, type_value: Type) -> io::Result<&mut MultiFile> {
        if !self.private_inputs_files.contains_key(&type_value) {
            self.private_inputs_files.insert(
                type_value.clone(),
                MultiFile::new(self.next_private_inputs_paths())?,
            );
        }
        Ok(self.private_inputs_files.get_mut(&type_value).unwrap())
    }

    fn get_relation_multi_file(&mut self) -> &mut MultiFile {
        &mut self.relation_file
    }
}

impl Sink for MultiFileSink {
    type Write = File;

    fn get_public_inputs_writer(&mut self, _: Type) -> zki_sieve_v3::Result<&mut Self::Write> {
        unimplemented!()
    }
    fn get_private_inputs_writer(&mut self, _: Type) -> zki_sieve_v3::Result<&mut Self::Write> {
        unimplemented!()
    }
    fn get_relation_writer(&mut self) -> &mut Self::Write {
        unimplemented!()
    }

    fn push_public_inputs_message(
        &mut self,
        public_inputs: &PublicInputs,
    ) -> zki_sieve_v3::Result<()> {
        let mf = self.get_public_inputs_multi_file(public_inputs.type_value.clone())?;
        public_inputs.write_into(&mut mf.create_file()?)
    }

    fn push_private_inputs_message(
        &mut self,
        private_inputs: &PrivateInputs,
    ) -> zki_sieve_v3::Result<()> {
        let mf = self.get_private_inputs_multi_file(private_inputs.type_value.clone())?;
        private_inputs.write_into(&mut mf.create_file()?)
    }

    fn push_relation_message(
        &mut self,
        relation: &Relation,
    ) -> zki_sieve_v3::Result<()> {
        let mf = self.get_relation_multi_file();
        relation.write_into(&mut mf.create_file()?)
    }
}
