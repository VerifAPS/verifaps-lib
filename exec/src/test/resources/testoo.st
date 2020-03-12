class A implements Z

method override MM
  var_input i : bool; end_var
end_method

end_class


interface Z

method MM
end_method

method error_body : bool
  error_body:= FALSE;
end_method

end_interface