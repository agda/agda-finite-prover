#!/usr/bin/ruby
Dir["src/**/*.agda"].each {|filename|
  dependencies = File.readlines(filename).grep(/^open import /).map {|line|
    line.chomp.split(/[( )]/)[2].gsub(".", "/")
  } + File.readlines(filename).grep(/^import /).map {|line|
    line.chomp.split(/[( )]/)[1].gsub(".", "/")
  }
  dependencies = dependencies.select {|d|
    File.exists?("src/#{d}.agda")
  }.map {|d|
    "crumbs/#{d}.agda"
  }
  
  agda_file = "crumbs/#{filename.gsub(/^src\//, "")}"
  dependencies = [filename] + dependencies
  puts "#{agda_file}: #{dependencies.join(" ")}"
  puts "\tmkdir -p #{File.dirname(agda_file)}"
  puts "\tcp $< $@"
}
