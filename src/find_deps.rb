#!/usr/bin/ruby
Dir["src/**/*.hs"].each {|filename|
  dependencies = File.readlines(filename).grep(/^import /).map {|line|
    "crumbs/#{line.chomp.split(/[( )]/)[-1].gsub(".", "/")}.agda"
  }.select {|f|
    File.exists?(f)
  }
  
  agda_file = "crumbs/#{filename.gsub(/^src\//, "").gsub(/\.hs$/, "")}.agda"
  puts "#{agda_file}: #{filename}"
  puts "\tmkdir -p #{File.dirname(agda_file)}"
  puts "\tcp $< $@"
  unless dependencies.empty?
    puts "#{agda_file}: #{dependencies.join(" ")}"
    puts "\ttouch $@"
  end
}
