# Rustdocs Release Process

There is [a script in place](../.maintain/rustdocs-release.sh) to manage the deployment of Substrate rustdocs at
https://paritytech.github.io/substrate, which is pushing the rustdocs file in `gh-pages` branch of
https://github.com/paritytech/substrate.

The documentation at the top of the `rustdocs-release.sh` explains most of the mechanics of the script.

Manage the rustdocs deployment with one of the following commands.

```bash
# Deploy rustdocs of `monthly-2021-10` tag
.maintain/rustdocs-release.sh deploy monthly-2021-10

# In addition to the above, the `latest` symlink will point to this version of rustdocs
.maintain/rustdocs-release.sh deploy -l monthly-2021-10

# Remove the rustdocs of `monthly-2021-10` from `gh-pages`.
.maintain/rustdocs-release.sh remove monthly-2021-10
```
