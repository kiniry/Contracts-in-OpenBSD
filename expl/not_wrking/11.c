// complete is not effective, although negative is missing, taking it in/out doesn't make a difference still proved.

#pragma JessieIntegerModel(exact)

/*@
    behavior zero:
        assumes a == 0;
        ensures \result == 0;

    behavior positive:
        assumes a > 0;
        ensures \result > 0;

   complete behaviors zero, positive;
*/
int abs(int a)
{
    if (a == 0)
        return 0;
    else if (a > 0)
        return a;
    else
        return -a;
}


