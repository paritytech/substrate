let repo = Git.self();
let templ_repo = Git.clone("https://github.com/substrate-developer-hub/substrate-node-template", "master");

for f in repo.ls("bin/node-template") {
  templ_repo.write(f, repo.read(f));
  templ_repo.add(f);
}


// TODO: update Cargo.toml

let result = cargo `check`;
if result.is_ok() {
  templ_repo.commit("Updating templates");
  // templ_repo.push();
  issue.comment("Committed the update");
} else {
  issue.comment("Cargo check failed: " += result.stderr);
}
