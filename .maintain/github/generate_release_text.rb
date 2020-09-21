# frozen_string_literal: true

require 'changelogerator'
require 'git'
require 'erb'

version = ENV['GITHUB_REF']
token = ENV['GITHUB_TOKEN']

substrate_path = ENV['GITHUB_WORKSPACE']
sg = Git.open(substrate_path)

# Generate an ERB renderer based on the template .erb file
renderer = ERB.new(
  File.read(ENV['GITHUB_WORKSPACE'] + '/.maintain/github/substrate_release.erb'),
  trim_mode: '<>'
)

last_version = sg
              .tags
              .map(&:name)
              .grep(/^v\d+\.\d+\.\d+.*$/)[-2]

changelog = Changelog.new(
  'paritytech/substrate', last_version, version, token: token
)

# Set all the variables needed for a release

misc_changes = changelog.changes_with_label('B1-releasenotes')
api_changes = changelog.changes_with_label('B3-apinoteworthy')
client_changes = changelog.changes_with_label('B5-clientnoteworthy')
runtime_changes = changelog.changes_with_label('B7-runtimenoteworthy')

puts renderer.result
