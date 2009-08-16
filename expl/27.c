//@ ensures \false;
void exit(int err_code)
{
  for(;;);
}
int main(void)
{
        static int rand_fd = -1;

        if (rand_fd < 0) {
                perror("open");
                exit(1);
        }
	    //@ assert rand_fd >= 0;


        return -1;
}
