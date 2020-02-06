<?php

chdir("lib");

$lib_files = get_lib_files();
$loaded_files = get_loaded_files();

$lib_files_index = array();
foreach($lib_files as $f) {
 $lib_files_index[$f] = 1;
}

$loaded_files_index = array();
foreach($loaded_files as $f) {
 $loaded_files_index[$f] = 1;
}

$missing_files = array();
$unloaded_files = array();
$extra_files = array();

$unloaded_header = "#@ Not autoload";
$n = strlen($unloaded_header);

foreach($lib_files as $f) {
 if (! array_key_exists($f,$loaded_files_index)) {
  $t = file_get_contents($f);
  if (strlen($t) >= $n && substr($t,0,$n) == $unloaded_header) {
   $unloaded_files[] = $f;
  } else {
   $extra_files[] = $f;
  }
 }
}

foreach($loaded_files as $f) {
 if (! array_key_exists($f,$lib_files_index)) {
  $missing_files[] = $f;
 }
}

if ($missing_files) {
 echo "Missing files:\r\n";
 foreach($missing_files as $f) {
  echo $f . PHP_EOL;
 }
 echo PHP_EOL . PHP_EOL;
}

if ($unloaded_files) {
 echo "Unloaded files:\r\n";
 foreach($unloaded_files as $f) {
  echo $f . PHP_EOL;
 }
 echo PHP_EOL . PHP_EOL;
}

if ($extra_files) {
 echo "Extra files:\r\n";
 foreach($extra_files as $f) {
  echo $f . PHP_EOL;
 }
 echo PHP_EOL . PHP_EOL;
}

exit;

//////////////////////////////////////////////////////////////////////

function get_lib_files() {
 $rii = new RecursiveIteratorIterator(new RecursiveDirectoryIterator("."));

 $files = array(); 

 foreach ($rii as $file) {
  if (! $file->isDir()){ 
   $p = $file->getPathname();
   $e = pathinfo($p,PATHINFO_EXTENSION);
   $p = str_replace('\\', '/', $p);
   if (strpos($p,'scratch/') !== false) {
    continue;
   }
   if (strlen($p) >= 2 && substr($p,0,2) == './') {
    $p = substr($p,2);
   }
   if ($e == 'mpl' && $p != '_ALL.mpl') {
    $files[] = $p;
   }
  }
 }

 return $files;
}

//////////////////////////////////////////////////////////////////////

function get_loaded_files() {
 $lines = preg_split("/\r\n|\n|\r/",file_get_contents("_ALL.mpl"));
 $files = array();
 $re = '/lib_read\("([A-Za-z0-9_\/]*\.mpl)"\)/';
 foreach($lines as $line) {
  if (preg_match($re,$line,$m)) {
   $files[] = $m[1];
  }
 }

 return $files;
}

?>