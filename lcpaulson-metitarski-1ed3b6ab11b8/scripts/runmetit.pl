#!/usr/bin/perl -w
#Runs MetiTarski on a list of files.

#Locates this script, resolving any symbolic links, allowing access to packaged modules.
use FindBin;
use lib "$FindBin::RealBin/lib";

use strict;
use English;   		#needed to refer to $BASETIME
use Getopt::Long;

#Package allowing the use of multiple threads, for parallel execution.
#Not in standard Perl distributions, and therefore packaged with this script.
use Parallel::ForkManager;

my (@pathcomps)=split(/\//, $0);   #components of pathname to script
my $cmdline = $pathcomps[-1];      #last is filename
foreach (@ARGV) {
  $cmdline .= /\s/ ? " '$_'" : " $_";
}

my $timelim=60;  #processor time limit
my $stdout = 0;
my $proofs = 0;
my $decimals=1;   #number of decimal places for runtimes
my $maxthreads = 2;
my $options = "";
my ($metitpath,$suffix, $tptp, $oldtmpfile);
GetOptions ('time=f' => \$timelim, 'threads=i' => \$maxthreads, 'decimals=i' => \$decimals, 'tptp=s' => \$tptp,
            'options=s' => \$options, 'oldtmpfile=s' => \$oldtmpfile, 'stdout' => \$stdout,
            'proofs' => \$proofs, 'suffix=s' => \$suffix, 'metitpath=s' => \$metitpath)
  or die "usage: [--time=f] [--threads=i] [--decimals=i] [--tptp=s] [--options=s] [--oldtmpfile=s] [--stdout] [--proofs] [--suffix=s] [--metitpath=s] <files>\n";

my $current_date = localtime;
my ($sec,$min,$hour,$mday,$mon,$year) = localtime;
my $yyyymmdd = sprintf "%4d-%02d-%02d", $year+1900, $mon+1, $mday;

my $switches = "--verbose 0 $options --time $timelim";
$proofs = 1 if ($options =~ /--tstp/);           #an implicit request for proofs
$switches .= $proofs ? " --show proof" : "";

#Threshold for a weight high enough to report
my $weightLimit = 600;

if (defined($tptp)) {
  unless (-d $tptp) { die "Invalid TPTP directory $tptp\n" }
  $switches .= " --tptp $tptp";
};

@ARGV = glob "*.tptp" if (@ARGV == 0); #no filenames given?  Default is all .tptp files
@ARGV = sort {lc $a cmp lc $b} @ARGV;  #ignore case

my $user = $ENV{USER};

#Create a separate copy of the executable, allowing this run to proceed undisturbed
chomp ($metitpath=`which metit`) unless (defined($metitpath));
my $metitbase="$user-metit$$";
my $metit="/tmp/$metitbase";
system "/bin/cp", $metitpath, $metit and die "Can't find the MT executable!";
  #                                  ^^^ system returns false on success, true on failure

my $file_labels = "-Metit-$yyyymmdd-$timelim$options";
$file_labels .= "-$suffix" if (defined($suffix));
$file_labels =~ tr/ /_/;

my $logfilename = "STATUS$file_labels.log";

my $tmpfilename = ".runmetit$$";
unless ($stdout) {
  open (LOGFILE, ">$logfilename") or die "Can't open the log file, $logfilename: $!";
}
open (TMPFILE, ">:unix", $tmpfilename) or die "Can't create the tmp file: $!";

my $proofdir = "Proofs$file_labels";
mkdir $proofdir, 0755 or die "Can't make the proof directory, $proofdir$: $!" if ($proofs);
my $proofpresent=0;

#Signal handling
$SIG{'HUP'} = 'IGNORE';
$SIG{'INT'} = 'clean_up';        # if keyboard interrupt, kill jobs and tmp files
sub clean_up {
  unlink $metit;
  unlink $tmpfilename;
  unlink $logfilename unless ($stdout);
  system "killall -INT $metitbase";
    # exec leaves qepcad running [due to multiple threads?]
  exit;
}

## Limiting processor time (although MetiTarski has a time-limit option)
my $inttimelim = int($timelim + 1.5);
my $limitcmd = "ulimit -S -t $inttimelim;";

##RUNNING THE PROOFS (IN PARALLEL)

#We use the fork manager to achieve parallelism, but there is a race condition
#  on the temporary file used to log the results. Lines can get lost or garbled.
#  Ideally, each thread should write to a separate log file.
my $manager = new Parallel::ForkManager( $maxthreads );

foreach my $file (@ARGV) {
  my (@pathcomps)=split(/\//, $file);   #components of pathname: last is filename
  my (@fncomps)=split(/\./, $pathcomps[-1]);
  pop (@fncomps);                       #delete filename extension
  my ($probname)=join(".", @fncomps);    #problem name is filename minus extension
  my $outcome = "UNKNOWN";  my $cputime=0;  my $rcftime=0;  my $wgt=0;
  #Re-use of an old temporary file from an aborted run
  my $entry = defined($oldtmpfile) ? `strings $oldtmpfile | grep '^$probname;'` : "";
  if ($entry =~ /[^;\s]+;[\w\s]+;[\d.]+;[\d.]+;[\d]+/) {
    #If a matching line was found of the right format, simply copy it to the new file.
    syswrite TMPFILE, "$entry";
  } else {
    $manager->start and next;
    open Metit, "$limitcmd $metit $switches $file |" or die "Can't launch metit: $!";
    while (<Metit>) {
      unless ($probname =~ /^[-+$%\w]+/) { die "Invalid problem name: $probname" }
      print STDOUT if (/File .* not found/ || /WARNING/);
      $outcome = "proved" if (/status Theorem/ || /status Unsatisfiable/);
      $outcome = "gave up" if (/status GaveUp/);
      $outcome = "timed out" if (/status Timeout/);
      $outcome = "*satisfiable*" if (/status CounterSatisfiable/ || /status Satisfiable/);
      $outcome = "ERROR" if (/status \w*Error/ || /ERROR/);
      $cputime = "$1" if (/Processor time:\s+([0-9.]+)/);
      $rcftime = "$1" if (/\s+([0-9.]+) \(QEPCAD\)/ || /\s+([0-9.]+) \(RCF\)/);
      $wgt = $1 if (/Maximum weight in proof search:\s+([0-9]+)/);
      if (/SZS output start CNFRefutation/) {
	$proofpresent=1;
	open TSTP, ">$proofdir/$probname.tstp"
	      or die "Can't open the proof output file, $proofdir/$probname.tstp: $!";
      }
      print TSTP "% " if (/SZS output/);   #Status lines must be commented out
      print TSTP if ($proofpresent);
      if (/SZS output end CNFRefutation/) {
	$proofpresent=0;
	close TSTP;
      }
    }
    close Metit;
    #An "error" after nearly exceeding the time limit is a actually a timeout.
    $outcome = "timed out" if ($outcome eq "ERROR" && $cputime * 1.2 > $timelim);
    print STDOUT ($outcome eq "proved" ? "$probname " : "($probname) ");
    #syswrite: trying to prevent a race condition
    syswrite TMPFILE, "$probname;$outcome;$cputime;$rcftime;$wgt\n";
    $manager->finish;
  }
}
$manager->wait_all_children;

chomp (my $hostname=`hostname -s`);
chomp (my $version=`$metit -v`);

#Now delete the copied executable
unlink $metit;

##GENERATING THE OUTPUT LOG

my $nproblems=0;  #total number of problems
my $nproved=0;    #number proved
my $ngaveup=0;    #number given up on
my $ntimedout=0;  #number timed out
my $nerrs=0;      #number of errors
my $cputime_fmt = ";%7.$decimals" . "f seconds";
my $maxTime=0;
my $totalTime=0;
my $totalRCFTime=0;

close TMPFILE;
if ($stdout) {
  print "\n";
} else {
  select LOGFILE;
  print "$version run on host $hostname ($current_date) with $switches; $maxthreads threads\n";
  print "Session ", $suffix, "\n" if (defined($suffix));
  print "Original command: $cmdline\n\n";
}

open TmpLog, "sort --ignore-case --ignore-nonprinting $tmpfilename |"
  or die "Can't open $tmpfilename: $!";
my $maxweightUsed=0;
while (<TmpLog>) {
  tr/\x00\x80-\xFF//d;  #delete any non-printing characters! (caused by file corruption)
  my ($probname,$outcome,$cputime,$rcftime,$wgt) =
      /([^;\s]+);([\w\s]+);([\d.]+);([\d.]+);([\d]+)/;
  next if (not (defined($probname)));
  print $probname, "; ", $outcome;
  if ($outcome eq "proved" || $outcome eq "gave up"|| $outcome eq "ERROR") {
    printf $cputime_fmt, $cputime;
    printf "$cputime_fmt (RCF)", $rcftime if (defined $cputime and $rcftime > 1 + $cputime/3);
  }
  print ", max weight = $wgt" if ($wgt >= $weightLimit);
  print "\n";
  $nproblems++;
  $nerrs++ if ($outcome eq "ERROR");
  $ngaveup++ if ($outcome eq "gave up");
  $ntimedout++ if ($outcome eq "timed out");
  if ($outcome eq "proved") {
    $nproved++;
    $totalTime+=$cputime;
    $totalRCFTime+=$rcftime;
    $maxweightUsed = $wgt if ($wgt > $maxweightUsed);
    $maxTime = $cputime if (defined $cputime and $cputime > $maxTime);
  }
}
close TmpLog;
unlink $tmpfilename;

##FINAL SUMMARY STATISTICS

if ($stdout) {
  printf "Proved %g problems out of %g or %2.0f percent\n",
    $nproved, $nproblems, 100 * $nproved / $nproblems;
  print "Errors: $nerrs\n" if ($nerrs > 0);
} else {
  print STDOUT "\nProved $nproved problems out of $nproblems\n";
  $sec = time - $BASETIME;
  use integer;
  $min  = $sec / 60;  $sec = $sec % 60;
  $hour = $min / 60;  $min   = $min   % 60;
  my $day  = $hour / 24; $hour  = $hour  % 24;

  print "\n";
  print "Maximum weight in successful proofs: $maxweightUsed\n";
  printf "Total cputime for proofs: %7.1f; %7.1f (RCF)\n", $totalTime, $totalRCFTime;
  printf "Maximum cputime: %7.1f\n", $maxTime;

  printf "Proved %g problems out of %g or %2.0f percent\n",
    $nproved, $nproblems, 100 * $nproved / $nproblems;
  print "Summary of failures: Gave Up, $ngaveup; Timed Out, $ntimedout; Error, $nerrs\n\n"
    if ($nproved < $nproblems);
  print "Elapsed time";
  printf " %d days", $day if ($day > 0);
  printf " %d:%02d:%02d\n", $hour, $min, $sec;

  # protect the log file!
  system "/bin/chmod", "444", $logfilename;
}
